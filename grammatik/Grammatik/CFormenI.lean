/-
  File:      Grammatik/CFormenI.lean
  Subject:   T4 pass (i): the correspondence relation between a Gabbro
             body and its emitted C, the near-neighbour forms with one
             correspondence lemma each, and `cCorr_block`.

  THE RELATION, per program point
    memory     `corrW EL σ st` (CSpeicher.lean section 12), under the
               emitter's layout given as data;
    locals     `EnvRel EL K ρG ρC`: every Gabbro variable of the context
               sits in the C local the certificate names (`K.vm`), encoded
               (`ValCorr`); C pointer parameters `T *restrict k` point to
               their table's block (`K.pp`); C parameters the Gabbro
               function does not carry have their fixed value (`K.ks`);
    outcomes   `StOut`: Gabbro `ok` is C normal completion, `zurueck` is
               `return` with the encoded answer, `leave`/`next` are the
               emitted `goto m_ende`/`goto m_weiter` of the innermost loop
               `m`; a Gabbro LOGIC or HARDWARE outcome carries no
               obligation (the checker proved it absent, or it is a named
               assumption), which is what a refinement of the non-error
               runs means.
  A C form CORRESPONDS to a Gabbro form when from related states the C
  form has a run that ends related to the Gabbro outcome (`ExprCorr`,
  `StmtCorr`). The C semantics is deterministic up to its oracles, so
  "has a run" is "its run" (the CUTS name the missing determinism proof).

  THE FORMS OF THIS PASS (emit.rs shapes, see `CFormen.lean`)
    E1  literal `100`                         Expr.lit            ecorr_lit
    E2  `true` / `false`                      wahr / falsch       ecorr_wahr/_falsch
    E3  local `x`                             var                 ecorr_var
    E4  (no C text: a range widening)         weiter              ecorr_weiter
    E5  `a + b`  (C's conversions, any width) add                 ecorr_add
    E6  `a - b`                               sub                 ecorr_sub
    E7  `a * b`                               mul                 ecorr_mul
    E8  `a / b`  (non-negative)               div                 ecorr_div
    E9  `a % b`  (non-negative)               rem                 ecorr_rem
    E10 `a / b`  (signed, truncating)         sdiv                ecorr_sdiv
    E11 `a % b`  (signed, truncating)         srem                ecorr_srem
    E12 `(a) & (b)`                           band                ecorr_band
    E13 `(a) | (b)`                           bor                 ecorr_bor
    E14 `(a) ^ (b)`                           bxor                ecorr_bxor
    E15 `(a) << (b)`                          shl                 ecorr_shl
    E16 `(a) >> (b)`                          shr                 ecorr_shr
    E17 `a < b`, `a <= b`, `a == b`           lt / le / eq        ecorr_lt/_le/_eq
        (`>`, `>=`, `!=` are Zucker.lean's gt/ge/ne over these)
    E18 `!(a)`                                nicht               ecorr_nicht
    E19 `(T)~(T)(x)`                          Expr.bnot (Zucker)  ecorr_bnot
    E20 `(T)(e)`  (verenge, a fitting cast)   (value unchanged)   ecorr_cast
    E21 `(T)(((uint32_t)(a) + (uint32_t)(b)) & mask)`   Zahl.addW  wrapC_add
    E22 `(T)(_gabbro_sat_u(…))`               Zahl.addS           satU_add
    E23 `T_speicher.slots[i].f`               slot (named table)  ecorr_slotNamed
    E24 `g` (plain static)                    glob                ecorr_glob
    E25 `g` (bare `_Atomic` name: seq_cst)    glob (atomic)       ecorr_globAtomar
    S1  `x = e;`                              assignVar           scorr_assignVar
    S2  `x += e;` `x -= e;` `x &= e;` `x |= e;`  Zucker plusGleich … scorr_plusGleich …
    S3  `T_speicher.slots[i].f = e;`          assignSlot          scorr_assignSlotNamed
    S4  `g = e;`                              assignGlob          scorr_assignGlob
    S5  `return e;` / `return;`               ret                 scorr_ret / ecorr_retEnd
    S6  `if (c) {…} else {…}` (`else if` is an `if` in the else arm)
                                              ite                 scorr_ite
    S7  `for (uint32_t v = 0; v < N; v += 1) { … m_weiter: ; } m_ende: ;`
                                              traverse            scorr_traverse
    S8  `T x = e;`, sequencing                Block.bind / cons   cCorr_block
-/
import Grammatik.CFormen
import Grammatik.Zucker

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. The value relation and the locals -/

/-- A Gabbro value and a C value correspond: integers, truth values,
    options and reasons by the emitter's encoding (`encW`), a pointer to
    table number `n` as a pointer to that table's block. -/
def ValCorr (EL : EmitLay D) : (τ : Ty) → Wert D τ → CVal → Prop
  | .int lo hi, v, c => c = .int (encW (.int lo hi) v)
  | .bool, v, c => c = .int (encW .bool v)
  | .opt n, v, c => c = .int (encW (.opt n) v)
  | .grund n, v, c => c = .int (encW (.grund n) v)
  | .ptr n _, _, c => ∃ t, D.tabNr n = some t ∧ c = .ptr ⟨.tab (EL.tnr t), 0⟩
  | .sum _, _, _ => False
  | .never, _, _ => False
  | .fl _ _, _, _ => False
  | .fnptr _, _, _ => False

theorem ValCorr.ne_undef {EL : EmitLay D} {τ : Ty} {v : Wert D τ}
    (h : ValCorr EL τ v .undef) : False := by
  cases τ <;> simp [ValCorr] at h

/-- The position of a variable in its context. -/
def Var.idx : {Γ : Ctx} → {τ : Ty} → Var Γ τ → Nat
  | _, _, .hier => 0
  | _, _, .dort x => Var.idx x + 1

theorem Var.idx_lt : ∀ {Γ : Ctx} {τ : Ty} (x : Var Γ τ), x.idx < Γ.length
  | _, _, .hier => by simp [Var.idx]
  | _, _, .dort x => by
      have := Var.idx_lt x
      simp only [Var.idx, List.length_cons]; omega

theorem Var.idx_inj : ∀ {Γ : Ctx} {τ τ' : Ty} (x : Var Γ τ) (y : Var Γ τ'),
    x.idx = y.idx → τ = τ' ∧ HEq x y
  | _, _, _, .hier, .hier, _ => ⟨rfl, HEq.rfl⟩
  | _, _, _, .hier, .dort _, h => by simp [Var.idx] at h
  | _, _, _, .dort _, .hier, h => by simp [Var.idx] at h
  | _, _, _, .dort x, .dort y, h => by
      obtain ⟨e, he⟩ := Var.idx_inj x y (by simp only [Var.idx] at h; omega)
      subst e
      cases he
      exact ⟨rfl, HEq.rfl⟩

theorem Env.get_set_same : ∀ {Γ : Ctx} {τ : Ty} (ρ : Env D Γ) (x : Var Γ τ) (v : Wert D τ),
    (ρ.set x v).get x = v
  | _, _, .cons _ _, .hier, _ => rfl
  | _, _, .cons _ ρ, .dort x, v => Env.get_set_same ρ x v

theorem Env.get_set_other : ∀ {Γ : Ctx} {τ τ' : Ty} (ρ : Env D Γ) (x : Var Γ τ) (v : Wert D τ)
    (y : Var Γ τ'), y.idx ≠ x.idx → (ρ.set x v).get y = ρ.get y
  | _, _, _, .cons _ _, .hier, _, .hier, h => absurd rfl h
  | _, _, _, .cons _ _, .hier, _, .dort _, _ => rfl
  | _, _, _, .cons _ _, .dort _, _, .hier, _ => rfl
  | _, _, _, .cons _ ρ, .dort x, v, .dort y, h =>
      Env.get_set_other ρ x v y (fun e => h (by simp only [Var.idx]; omega))

/-- The certificate's layout of the C locals at a program point: where
    each Gabbro variable of the context lives (`vm`, by position), which
    C locals are pointer parameters to which table (`pp`), and which C
    locals the Gabbro function does not have and hold a fixed value (`ks`,
    e.g. an index parameter the model fixes). -/
structure CEnvLay (D : Deklaration) (Γ : Ctx) where
  vm : List Nat
  pp : List (Nat × D.Tab)
  ks : List (Nat × Int)

namespace CEnvLay
variable {Γ : Ctx}

/-- The C local of a Gabbro variable. -/
def loc (K : CEnvLay D Γ) {τ : Ty} (x : Var Γ τ) : Nat := K.vm.getD x.idx 0

/-- A `let` binds the next variable to C local `x`. -/
def push (K : CEnvLay D Γ) (τ : Ty) (x : Nat) : CEnvLay D (τ :: Γ) := ⟨x :: K.vm, K.pp, K.ks⟩

/-- Well-formed: one C local per variable, all distinct, none of them a
    pointer or fixed parameter. Checked by `decide` on a certificate. -/
def okB (K : CEnvLay D Γ) : Bool :=
  decide (K.vm.length = Γ.length) && decide K.vm.Nodup &&
    K.vm.all (fun y => K.pp.all (fun q => q.1 != y) && K.ks.all (fun q => q.1 != y))

/-- A fresh C local for a `let`. -/
def freshB (K : CEnvLay D Γ) (x : Nat) : Bool :=
  !(K.vm.contains x) && K.pp.all (fun q => q.1 != x) && K.ks.all (fun q => q.1 != x)

end CEnvLay

/-- THE LOCALS RELATION. -/
def EnvRel (EL : EmitLay D) {Γ : Ctx} (K : CEnvLay D Γ) (ρG : Env D Γ) (ρC : CLok) : Prop :=
  (∀ (τ : Ty) (x : Var Γ τ), ValCorr EL τ (ρG.get x) (ρC (K.loc x))) ∧
  (∀ q ∈ K.pp, ρC q.1 = .ptr ⟨.tab (EL.tnr q.2), 0⟩) ∧
  (∀ q ∈ K.ks, ρC q.1 = .int q.2)

theorem okB_spec {Γ : Ctx} {K : CEnvLay D Γ} (h : K.okB = true) :
    K.vm.length = Γ.length ∧ K.vm.Nodup ∧
      (∀ y ∈ K.vm, (∀ q ∈ K.pp, q.1 ≠ y) ∧ (∀ q ∈ K.ks, q.1 ≠ y)) := by
  unfold CEnvLay.okB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, bne_iff_ne, ne_eq] at h
  exact ⟨h.1.1, h.1.2, fun y hy => ⟨h.2 y hy |>.1, h.2 y hy |>.2⟩⟩

theorem freshB_spec {Γ : Ctx} {K : CEnvLay D Γ} {x : Nat} (h : K.freshB x = true) :
    x ∉ K.vm ∧ (∀ q ∈ K.pp, q.1 ≠ x) ∧ (∀ q ∈ K.ks, q.1 ≠ x) := by
  unfold CEnvLay.freshB at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not,
    List.all_eq_true, bne_iff_ne, ne_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem loc_mem {Γ : Ctx} {K : CEnvLay D Γ} (hl : K.vm.length = Γ.length) {τ : Ty}
    (x : Var Γ τ) : K.loc x ∈ K.vm := by
  unfold CEnvLay.loc
  have := Var.idx_lt x
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
  exact List.getElem_mem _

theorem loc_ne {Γ : Ctx} {K : CEnvLay D Γ} (hl : K.vm.length = Γ.length) (hn : K.vm.Nodup)
    {τ τ' : Ty} (x : Var Γ τ) (y : Var Γ τ') (h : y.idx ≠ x.idx) : K.loc y ≠ K.loc x := by
  unfold CEnvLay.loc
  have hx := Var.idx_lt x
  have hy := Var.idx_lt y
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega),
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
  intro e
  apply h
  have e' : K.vm[y.idx]? = K.vm[x.idx]? := by
    rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)]
    exact congrArg some e
  exact (List.getElem?_inj (by omega) hn).mp e'

/-- Writing a Gabbro variable and its C local keeps the relation. -/
theorem envRel_set {EL : EmitLay D} {Γ : Ctx} {K : CEnvLay D Γ} (hK : K.okB = true)
    {ρG : Env D Γ} {ρC : CLok} (h : EnvRel EL K ρG ρC) {τ : Ty} (x : Var Γ τ)
    (v : Wert D τ) (c : CVal) (hv : ValCorr EL τ v c) :
    EnvRel EL K (ρG.set x v) (lokUpd ρC (K.loc x) c) := by
  obtain ⟨hl, hn, hd⟩ := okB_spec hK
  refine ⟨?_, ?_, ?_⟩
  · intro τ' y
    by_cases hi : y.idx = x.idx
    · obtain ⟨e, he⟩ := Var.idx_inj y x hi
      subst e
      cases he
      rw [Env.get_set_same]
      simp only [lokUpd, if_pos]
      exact hv
    · rw [Env.get_set_other _ _ _ _ hi]
      simp only [lokUpd]
      rw [if_neg (loc_ne hl hn x y hi)]
      exact h.1 τ' y
  · intro q hq
    simp only [lokUpd]
    rw [if_neg ((hd _ (loc_mem hl x)).1 q hq)]
    exact h.2.1 q hq
  · intro q hq
    simp only [lokUpd]
    rw [if_neg ((hd _ (loc_mem hl x)).2 q hq)]
    exact h.2.2 q hq

/-- A `let` into a fresh C local extends the relation. -/
theorem envRel_push {EL : EmitLay D} {Γ : Ctx} {K : CEnvLay D Γ} (hK : K.okB = true) {x : Nat}
    (hf : K.freshB x = true) {ρG : Env D Γ} {ρC : CLok} (h : EnvRel EL K ρG ρC) {τ : Ty}
    (v : Wert D τ) (c : CVal) (hv : ValCorr EL τ v c) :
    EnvRel EL (K.push τ x) (.cons v ρG) (lokUpd ρC x c) := by
  obtain ⟨hx, hp, hk⟩ := freshB_spec hf
  obtain ⟨hl, -, -⟩ := okB_spec hK
  refine ⟨?_, ?_, ?_⟩
  · intro τ' y
    cases y with
    | hier =>
        show ValCorr EL τ v (lokUpd ρC x c x)
        simp only [lokUpd, if_pos]
        exact hv
    | dort y =>
        show ValCorr EL τ' (ρG.get y) (lokUpd ρC x c (K.loc y))
        have hne : K.loc y ≠ x := fun e => hx (e ▸ loc_mem hl y)
        simp only [lokUpd]
        rw [if_neg hne]
        exact h.1 τ' y
  · intro q hq
    simp only [lokUpd]
    rw [if_neg (hp q hq)]
    exact h.2.1 q hq
  · intro q hq
    simp only [lokUpd]
    rw [if_neg (hk q hq)]
    exact h.2.2 q hq

/-! ## 2. The correspondence judgements -/

/-- What a correspondence is stated under: the emitter's layout and the C
    side's oracles and call meanings (device oracle, frame number, calls
    to the unit's functions `CR`, foreign calls `XR`), and the Gabbro
    side's (`Orakel`, `forever` passes, the call meaning `R`). -/
structure TVCtx (D : Deklaration) where
  EL : EmitLay D
  orc : DevOrc
  fr : Nat
  CR : CCallR
  XR : CCallR
  O : Orakel D
  passes : Nat
  R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f

theorem corrW_same {EL : EmitLay D} {σ : World D} {st st' : CSt} (h : corrW EL σ st)
    (hs : SameML st st') : corrW EL σ st' := by
  obtain ⟨hm, hl⟩ := hs
  unfold corrW
  rw [hm, hl]
  exact h

/-- EXPRESSION CORRESPONDENCE: from related states the C expression
    evaluates to the encoding of the Gabbro value. -/
def ExprCorr (X : TVCtx D) {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} (K : CEnvLay D Γ) (c : CX)
    (e : Expr D Γ Λ τ) : Prop :=
  ∀ (σ : World D) (st : CSt) (ρG : Env D Γ) (ρC : CLok), corrW X.EL σ st →
    EnvRel X.EL K ρG ρC →
    ∃ v st', ev X.EL.lay X.orc X.fr c st ρC = some (v, st') ∧ ValCorr X.EL τ (eval σ e σ ρG) v

/-- A Gabbro outcome that is an error: a logic clause or a hardware
    assumption failed. It carries no obligation for the C side. -/
def Ausgang.istFehler {V : Vertrag D} {l : Bool} {Γ : Ctx} : Ausgang V l Γ → Bool
  | .logik _ => true
  | .hardware _ => true
  | _ => false

/-- The answer of a `return`. -/
def RetCorr (EL : EmitLay D) : (e : Option Ty) → ErgVal D e → Option CVal → Prop
  | none, _, cv => cv = none
  | some τ, v, cv => ∃ c, cv = some c ∧ ValCorr EL τ v c

/-- THE OUTCOME RELATION of a statement inside loop `m` (the innermost
    enclosing loop's mark; `leave`/`next` lower to `goto m_ende`/`goto
    m_weiter`, emit.rs 9235). -/
def StOut (X : TVCtx D) (m : Nat) {Γ : Ctx} (K : CEnvLay D Γ) {V : Vertrag D} {l : Bool} :
    Ausgang V l Γ → COut → Prop
  | .ok σ' ρG', o => ∃ st' ρC', o = .norm st' ρC' ∧ corrW X.EL σ' st' ∧ EnvRel X.EL K ρG' ρC'
  | .zurueck σ' v, o => ∃ st' cv, o = .ret st' cv ∧ corrW X.EL σ' st' ∧ RetCorr X.EL V.erg v cv
  | .grund _ _, _ => False
  | .leave _ σ' ρG', o =>
      ∃ st' ρC', o = .jump (.ende m) st' ρC' ∧ corrW X.EL σ' st' ∧ EnvRel X.EL K ρG' ρC'
  | .next _ σ' ρG', o =>
      ∃ st' ρC', o = .jump (.weiter m) st' ρC' ∧ corrW X.EL σ' st' ∧ EnvRel X.EL K ρG' ρC'
  | .logik _, _ => False
  | .hardware _, _ => False

/-- STATEMENT CORRESPONDENCE: from related states, unless the Gabbro
    statement ends in an error, the C statement has a run whose outcome is
    related to the Gabbro outcome. -/
def StmtCorr (X : TVCtx D) (m : Nat) {Γ : Ctx} (K : CEnvLay D Γ) {V : Vertrag D} {l : Bool}
    {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ') (cs : CS) : Prop :=
  ∀ (σ : World D) (st : CSt) (ρG : Env D Γ) (ρC : CLok), corrW X.EL σ st →
    EnvRel X.EL K ρG ρC → (execStmt X.O X.passes X.R s σ ρG).istFehler = false →
    ∃ o, Exec X.EL.lay X.orc X.fr X.CR X.XR cs st ρC o ∧
      StOut X m K (execStmt X.O X.passes X.R s σ ρG) o

/-- BLOCK CORRESPONDENCE, the same judgement for `execBlock`. -/
def BlockSem (X : TVCtx D) (m : Nat) {Γ : Ctx} (K : CEnvLay D Γ) {V : Vertrag D} {l : Bool}
    {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ') (cs : CS) : Prop :=
  ∀ (σ : World D) (st : CSt) (ρG : Env D Γ) (ρC : CLok), corrW X.EL σ st →
    EnvRel X.EL K ρG ρC → (execBlock X.O X.passes X.R b σ ρG).istFehler = false →
    ∃ o, Exec X.EL.lay X.orc X.fr X.CR X.XR cs st ρC o ∧
      StOut X m K (execBlock X.O X.passes X.R b σ ρG) o

/-! ## 3. Pass (i): expressions -/

section Ausdruck

variable (X : TVCtx D) {Γ : Ctx} {Λ : List (Res D)} (K : CEnvLay D Γ)

/-- Running a corresponding expression: its value, and a state still
    related (expressions change no memory). -/
theorem ExprCorr.run {τ : Ty} {c : CX} {e : Expr D Γ Λ τ} (h : ExprCorr X K c e)
    {σ : World D} {st : CSt} {ρG : Env D Γ} {ρC : CLok} (hc : corrW X.EL σ st)
    (he : EnvRel X.EL K ρG ρC) :
    ∃ v st', ev X.EL.lay X.orc X.fr c st ρC = some (v, st') ∧
      ValCorr X.EL τ (eval σ e σ ρG) v ∧ corrW X.EL σ st' := by
  obtain ⟨v, st', h1, h2⟩ := h σ st ρG ρC hc he
  exact ⟨v, st', h1, h2, corrW_same hc (ev_same _ _ _ _ _ _ _ _ h1)⟩

/-- The same for an integer expression: its value is the number. -/
theorem ExprCorr.runI {lo hi : Int} {c : CX} {e : Expr D Γ Λ (.int lo hi)}
    (h : ExprCorr X K c e) {σ : World D} {st : CSt} {ρG : Env D Γ} {ρC : CLok}
    (hc : corrW X.EL σ st) (he : EnvRel X.EL K ρG ρC) :
    ∃ st', ev X.EL.lay X.orc X.fr c st ρC = some (.int (eval σ e σ ρG).n, st') ∧
      corrW X.EL σ st' := by
  obtain ⟨v, st', h1, h2, h3⟩ := h.run X K hc he
  have e2 : v = .int (eval σ e σ ρG).n := h2
  subst e2
  exact ⟨st', h1, h3⟩

/-- The same for a truth value: `1` or `0`. -/
theorem ExprCorr.runB {c : CX} {e : Expr D Γ Λ .bool}
    (h : ExprCorr X K c e) {σ : World D} {st : CSt} {ρG : Env D Γ} {ρC : CLok}
    (hc : corrW X.EL σ st) (he : EnvRel X.EL K ρG ρC) :
    ∃ st', ev X.EL.lay X.orc X.fr c st ρC = some (.int (b2i (wahr? (eval σ e σ ρG))), st') ∧
      corrW X.EL σ st' := by
  obtain ⟨v, st', h1, h2, h3⟩ := h.run X K hc he
  have e2 : v = .int (b2i (wahr? (eval σ e σ ρG))) := h2
  subst e2
  exact ⟨st', h1, h3⟩

theorem truth_b2i (b : Bool) : truth (.int (b2i b)) = some b := by
  cases b <;> rfl

/-- E1. A decimal literal. -/
theorem ecorr_lit (n : Int) : ExprCorr X K (.lit n) (Expr.lit (D := D) (Γ := Γ) (Λ := Λ) n) := by
  intro σ st ρG ρC _ _
  exact ⟨.int n, st, rfl, rfl⟩

/-- E2. `true` is `1`, `false` is `0` (`<stdbool.h>`). -/
theorem ecorr_wahr : ExprCorr X K (.lit 1) (Expr.wahr (D := D) (Γ := Γ) (Λ := Λ)) := by
  intro σ st ρG ρC _ _
  exact ⟨.int 1, st, rfl, rfl⟩

theorem ecorr_falsch : ExprCorr X K (.lit 0) (Expr.falsch (D := D) (Γ := Γ) (Λ := Λ)) := by
  intro σ st ρG ρC _ _
  exact ⟨.int 0, st, rfl, rfl⟩

/-- E3. A local: the C local the certificate names for the variable. -/
theorem ecorr_var {τ : Ty} (x : Var Γ τ) :
    ExprCorr X K (.var (K.loc x)) (Expr.var (D := D) (Λ := Λ) x) := by
  intro σ st ρG ρC _ he
  have hv := he.1 τ x
  refine ⟨ρC (K.loc x), st, ?_, hv⟩
  cases hy : ρC (K.loc x) with
  | undef => rw [hy] at hv; exact (ValCorr.ne_undef hv).elim
  | int n => simp [ev, hy]
  | ptr p => simp [ev, hy]

/-- E4. A widening has no C text. -/
theorem ecorr_weiter {lo hi lo' hi' : Int} {c : CX} {e : Expr D Γ Λ (.int lo hi)}
    (h1 : lo' ≤ lo) (h2 : hi ≤ hi') (h : ExprCorr X K c e) :
    ExprCorr X K c (Expr.weiter h1 h2 e) := by
  intro σ st ρG ρC hc he
  obtain ⟨st', hv, -⟩ := h.runI X K hc he
  exact ⟨_, st', hv, rfl⟩

/-- The binary-operator scheme: both operands correspond and lie in the
    computation type `t`, so C's conversions keep them; the C operator
    then computes the Gabbro value. Every arithmetic form below is this
    scheme with its operator fact. -/
theorem ecorr_binop (op : CBinOp) (t : CIT) {l1 h1 l2 h2 lo hi : Int} {ca cb : CX}
    {a : Expr D Γ Λ (.int l1 h1)} {b : Expr D Γ Λ (.int l2 h2)} {e : Expr D Γ Λ (.int lo hi)}
    (ha : ExprCorr X K ca a) (hb : ExprCorr X K cb b) (hta : t.holds l1 h1) (htb : t.holds l2 h2)
    (hop : ∀ (σ : World D) (ρG : Env D Γ),
      cArith op t (eval σ a σ ρG).n (eval σ b σ ρG).n = some (eval σ e σ ρG).n) :
    ExprCorr X K (.bin op t ca cb) e := by
  intro σ st ρG ρC hc he
  obtain ⟨st1, h1', hc1⟩ := ha.runI X K hc he
  obtain ⟨st2, h2', -⟩ := hb.runI X K hc1 he
  have ra := (eval σ a σ ρG).lo_le
  have ra' := (eval σ a σ ρG).le_hi
  have rb := (eval σ b σ ρG).lo_le
  have rb' := (eval σ b σ ρG).le_hi
  have ca' : conv t (eval σ a σ ρG).n = some (eval σ a σ ρG).n :=
    conv_id ⟨by have := hta.1; omega, by have := hta.2; omega⟩
  have cb' : conv t (eval σ b σ ρG).n = some (eval σ b σ ρG).n :=
    conv_id ⟨by have := htb.1; omega, by have := htb.2; omega⟩
  refine ⟨.int (eval σ e σ ρG).n, st2, ?_, rfl⟩
  simp only [ev, h1', h2', ca', cb', hop σ ρG]

/-- E5. `a + b` in computation type `t` (`M104`: the result range lies in
    `t`). -/
theorem ecorr_add (t : CIT) {l1 h1 l2 h2 : Int} {ca cb : CX}
    {a : Expr D Γ Λ (.int l1 h1)} {b : Expr D Γ Λ (.int l2 h2)}
    (ha : ExprCorr X K ca a) (hb : ExprCorr X K cb b) (hta : t.holds l1 h1) (htb : t.holds l2 h2)
    (htr : t.holds (l1 + l2) (h1 + h2)) : ExprCorr X K (.bin .add t ca cb) (.add a b) :=
  ecorr_binop X K .add t ha hb hta htb (fun σ ρG => by
    have r1 : l1 + l2 ≤ (eval σ a σ ρG).n + (eval σ b σ ρG).n := (eval σ (Expr.add a b) σ ρG).lo_le
    have r2 : (eval σ a σ ρG).n + (eval σ b σ ρG).n ≤ h1 + h2 := (eval σ (Expr.add a b) σ ρG).le_hi
    exact conv_id ⟨by have := htr.1; omega, by have := htr.2; omega⟩)

/-- E6. `a - b`. -/
theorem ecorr_sub (t : CIT) {l1 h1 l2 h2 : Int} {ca cb : CX}
    {a : Expr D Γ Λ (.int l1 h1)} {b : Expr D Γ Λ (.int l2 h2)}
    (ha : ExprCorr X K ca a) (hb : ExprCorr X K cb b) (hta : t.holds l1 h1) (htb : t.holds l2 h2)
    (htr : t.holds (l1 - h2) (h1 - l2)) : ExprCorr X K (.bin .sub t ca cb) (.sub a b) :=
  ecorr_binop X K .sub t ha hb hta htb (fun σ ρG => by
    have r1 : l1 - h2 ≤ (eval σ a σ ρG).n - (eval σ b σ ρG).n := (eval σ (Expr.sub a b) σ ρG).lo_le
    have r2 : (eval σ a σ ρG).n - (eval σ b σ ρG).n ≤ h1 - l2 := (eval σ (Expr.sub a b) σ ρG).le_hi
    exact conv_id ⟨by have := htr.1; omega, by have := htr.2; omega⟩)

/-- E7. `a * b`. -/
theorem ecorr_mul (t : CIT) {l1 h1 l2 h2 : Int} {ca cb : CX}
    {a : Expr D Γ Λ (.int l1 h1)} {b : Expr D Γ Λ (.int l2 h2)}
    (ha : ExprCorr X K ca a) (hb : ExprCorr X K cb b) (hta : t.holds l1 h1) (htb : t.holds l2 h2)
    (htr : t.holds (imin (imin (l1*l2) (l1*h2)) (imin (h1*l2) (h1*h2)))
      (imax (imax (l1*l2) (l1*h2)) (imax (h1*l2) (h1*h2)))) :
    ExprCorr X K (.bin .mul t ca cb) (.mul a b) :=
  ecorr_binop X K .mul t ha hb hta htb (fun σ ρG => by
    have r1 : imin (imin (l1*l2) (l1*h2)) (imin (h1*l2) (h1*h2)) ≤
        (eval σ a σ ρG).n * (eval σ b σ ρG).n := (eval σ (Expr.mul a b) σ ρG).lo_le
    have r2 : (eval σ a σ ρG).n * (eval σ b σ ρG).n ≤
        imax (imax (l1*l2) (l1*h2)) (imax (h1*l2) (h1*h2)) := (eval σ (Expr.mul a b) σ ρG).le_hi
    exact conv_id ⟨by have := htr.1; omega, by have := htr.2; omega⟩)

/-- E8. `a / b` over a non-negative dividend and a positive divisor: C's
    truncation is Gabbro's `tdiv`. -/
theorem ecorr_div (t : CIT) {l1 h1 l2 h2 : Int} {ca cb : CX} (h0 : 0 ≤ l1) (h1' : 1 ≤ l2)
    {a : Expr D Γ Λ (.int l1 h1)} {b : Expr D Γ Λ (.int l2 h2)}
    (ha : ExprCorr X K ca a) (hb : ExprCorr X K cb b) (hta : t.holds l1 h1) (htb : t.holds l2 h2) :
    ExprCorr X K (.bin .div t ca cb) (.div h0 h1' a b) :=
  ecorr_binop X K .div t ha hb hta htb (fun σ ρG => by
    have rb := (eval σ b σ ρG).lo_le
    show (if (eval σ b σ ρG).n = 0 ∨ (t.sgn = true ∧ (eval σ a σ ρG).n = t.lo ∧
      (eval σ b σ ρG).n = -1) then none else some ((eval σ a σ ρG).n.tdiv (eval σ b σ ρG).n)) = _
    rw [if_neg (by omega)]
    rfl)

/-- E9. `a % b`, same conditions. -/
theorem ecorr_rem (t : CIT) {l1 h1 l2 h2 : Int} {ca cb : CX} (h0 : 0 ≤ l1) (h1' : 1 ≤ l2)
    {a : Expr D Γ Λ (.int l1 h1)} {b : Expr D Γ Λ (.int l2 h2)}
    (ha : ExprCorr X K ca a) (hb : ExprCorr X K cb b) (hta : t.holds l1 h1) (htb : t.holds l2 h2) :
    ExprCorr X K (.bin .mod t ca cb) (.rem h0 h1' a b) :=
  ecorr_binop X K .mod t ha hb hta htb (fun σ ρG => by
    have rb := (eval σ b σ ρG).lo_le
    show (if (eval σ b σ ρG).n = 0 ∨ (t.sgn = true ∧ (eval σ a σ ρG).n = t.lo ∧
      (eval σ b σ ρG).n = -1) then none else some ((eval σ a σ ρG).n.tmod (eval σ b σ ρG).n)) = _
    rw [if_neg (by omega)]
    rfl)

/-- E10. Signed `a / b`: truncating (the lane-128 semantics would round
    toward minus infinity here). `INT_MIN / -1` is excluded by the
    dividend's range (`hmin`, implied by `M104` on the result). -/
theorem ecorr_sdiv (t : CIT) {l1 h1 l2 h2 : Int} {ca cb : CX} (hb0 : 1 ≤ l2 ∨ h2 ≤ -1)
    {a : Expr D Γ Λ (.int l1 h1)} {b : Expr D Γ Λ (.int l2 h2)}
    (ha : ExprCorr X K ca a) (hb : ExprCorr X K cb b) (hta : t.holds l1 h1) (htb : t.holds l2 h2)
    (hmin : t.sgn = true → t.lo < l1) :
    ExprCorr X K (.bin .div t ca cb) (.sdiv hb0 a b) :=
  ecorr_binop X K .div t ha hb hta htb (fun σ ρG => by
    have ra := (eval σ a σ ρG).lo_le
    have rb := (eval σ b σ ρG).lo_le
    have rb' := (eval σ b σ ρG).le_hi
    show (if (eval σ b σ ρG).n = 0 ∨ (t.sgn = true ∧ (eval σ a σ ρG).n = t.lo ∧
      (eval σ b σ ρG).n = -1) then none else some ((eval σ a σ ρG).n.tdiv (eval σ b σ ρG).n)) = _
    rw [if_neg (by
      intro hc
      rcases hc with hc | ⟨hs, hc, -⟩
      · omega
      · have := hmin hs; omega)]
    rfl)

/-- E11. Signed `a % b` (`INT_MIN % -1` is UB in C11 as well). -/
theorem ecorr_srem (t : CIT) {l1 h1 l2 h2 : Int} {ca cb : CX} (hb0 : 1 ≤ l2 ∨ h2 ≤ -1)
    {a : Expr D Γ Λ (.int l1 h1)} {b : Expr D Γ Λ (.int l2 h2)}
    (ha : ExprCorr X K ca a) (hb : ExprCorr X K cb b) (hta : t.holds l1 h1) (htb : t.holds l2 h2)
    (hmin : t.sgn = true → t.lo < l1) :
    ExprCorr X K (.bin .mod t ca cb) (.srem hb0 a b) :=
  ecorr_binop X K .mod t ha hb hta htb (fun σ ρG => by
    have ra := (eval σ a σ ρG).lo_le
    have rb := (eval σ b σ ρG).lo_le
    have rb' := (eval σ b σ ρG).le_hi
    show (if (eval σ b σ ρG).n = 0 ∨ (t.sgn = true ∧ (eval σ a σ ρG).n = t.lo ∧
      (eval σ b σ ρG).n = -1) then none else some ((eval σ a σ ρG).n.tmod (eval σ b σ ρG).n)) = _
    rw [if_neg (by
      intro hc
      rcases hc with hc | ⟨hs, hc, -⟩
      · omega
      · have := hmin hs; omega)]
    rfl)

/-- E12. `(a) & (b)` over `0 ..` (`M137`), in any signedness. -/
theorem ecorr_band (t : CIT) {l1 h1 l2 h2 : Int} {ca cb : CX} (h0 : 0 ≤ l1) (h0' : 0 ≤ l2)
    {a : Expr D Γ Λ (.int l1 h1)} {b : Expr D Γ Λ (.int l2 h2)}
    (ha : ExprCorr X K ca a) (hb : ExprCorr X K cb b) (hta : t.holds l1 h1) (htb : t.holds l2 h2) :
    ExprCorr X K (.bin .band t ca cb) (.band h0 h0' a b) :=
  ecorr_binop X K .band t ha hb hta htb (fun σ ρG => by
    have ra := (eval σ a σ ρG).lo_le
    have rb := (eval σ b σ ρG).lo_le
    show (if 0 ≤ (eval σ a σ ρG).n ∧ 0 ≤ (eval σ b σ ρG).n then
      some (((eval σ a σ ρG).n.toNat &&& (eval σ b σ ρG).n.toNat : Nat) : Int) else none) = _
    rw [if_pos ⟨by omega, by omega⟩]
    rfl)

/-- E13. `(a) | (b)`. -/
theorem ecorr_bor (t : CIT) (w : Nat) {l1 h1 l2 h2 : Int} {ca cb : CX} (h0 : 0 ≤ l1)
    (h0' : 0 ≤ l2) (hw1 : h1 < 2 ^ w) (hw2 : h2 < 2 ^ w)
    {a : Expr D Γ Λ (.int l1 h1)} {b : Expr D Γ Λ (.int l2 h2)}
    (ha : ExprCorr X K ca a) (hb : ExprCorr X K cb b) (hta : t.holds l1 h1) (htb : t.holds l2 h2) :
    ExprCorr X K (.bin .bor t ca cb) (.bor w h0 h0' hw1 hw2 a b) :=
  ecorr_binop X K .bor t ha hb hta htb (fun σ ρG => by
    have ra := (eval σ a σ ρG).lo_le
    have rb := (eval σ b σ ρG).lo_le
    show (if 0 ≤ (eval σ a σ ρG).n ∧ 0 ≤ (eval σ b σ ρG).n then
      some (((eval σ a σ ρG).n.toNat ||| (eval σ b σ ρG).n.toNat : Nat) : Int) else none) = _
    rw [if_pos ⟨by omega, by omega⟩]
    rfl)

/-- E14. `(a) ^ (b)`. -/
theorem ecorr_bxor (t : CIT) (w : Nat) {l1 h1 l2 h2 : Int} {ca cb : CX} (h0 : 0 ≤ l1)
    (h0' : 0 ≤ l2) (hw1 : h1 < 2 ^ w) (hw2 : h2 < 2 ^ w)
    {a : Expr D Γ Λ (.int l1 h1)} {b : Expr D Γ Λ (.int l2 h2)}
    (ha : ExprCorr X K ca a) (hb : ExprCorr X K cb b) (hta : t.holds l1 h1) (htb : t.holds l2 h2) :
    ExprCorr X K (.bin .bxor t ca cb) (.bxor w h0 h0' hw1 hw2 a b) :=
  ecorr_binop X K .bxor t ha hb hta htb (fun σ ρG => by
    have ra := (eval σ a σ ρG).lo_le
    have rb := (eval σ b σ ρG).lo_le
    show (if 0 ≤ (eval σ a σ ρG).n ∧ 0 ≤ (eval σ b σ ρG).n then
      some (((eval σ a σ ρG).n.toNat ^^^ (eval σ b σ ρG).n.toNat : Nat) : Int) else none) = _
    rw [if_pos ⟨by omega, by omega⟩]
    rfl)

theorem two_pow_le_two_pow {m n : Nat} (h : m ≤ n) : (2 : Int) ^ m ≤ 2 ^ n := by
  have := Nat.pow_le_pow_right (show 0 < 2 by decide) h
  have e1 : ((2 ^ m : Nat) : Int) = (2 : Int) ^ m := by simp
  have e2 : ((2 ^ n : Nat) : Int) = (2 : Int) ^ n := by simp
  omega

/-- E15. `(a) << (b)`: the count below the computation width (`hsh`), the
    result in `t` (`M104`). -/
theorem ecorr_shl (t : CIT) (w : Nat) {l1 h1 l2 h2 : Int} {ca cb : CX} (hw1 : h1 < 2 ^ w)
    (hw2 : h2 < (w : Int)) (h0 : 0 ≤ l1) (h0' : 0 ≤ l2)
    {a : Expr D Γ Λ (.int l1 h1)} {b : Expr D Γ Λ (.int l2 h2)}
    (ha : ExprCorr X K ca a) (hb : ExprCorr X K cb b) (hta : t.holds l1 h1) (htb : t.holds l2 h2)
    (hsh : h2 < (t.bits : Int)) (htr : t.holds 0 (h1 * 2 ^ h2.toNat)) :
    ExprCorr X K (.bin .shl t ca cb) (.shl w hw1 hw2 h0 h0' a b) :=
  ecorr_binop X K .shl t ha hb hta htb (fun σ ρG => by
    have ra := (eval σ a σ ρG).lo_le
    have rb := (eval σ b σ ρG).lo_le
    have rb' := (eval σ b σ ρG).le_hi
    have r2 : (eval σ a σ ρG).n * 2 ^ (eval σ b σ ρG).n.toNat ≤ h1 * 2 ^ h2.toNat :=
      (eval σ (Expr.shl w hw1 hw2 h0 h0' a b) σ ρG).le_hi
    have r1 : 0 ≤ (eval σ a σ ρG).n * 2 ^ (eval σ b σ ρG).n.toNat :=
      (eval σ (Expr.shl w hw1 hw2 h0 h0' a b) σ ρG).lo_le
    show (if 0 ≤ (eval σ b σ ρG).n ∧ (eval σ b σ ρG).n < (t.bits : Int) ∧ 0 ≤ (eval σ a σ ρG).n then
      (if t.sgn = true then
        (if (eval σ a σ ρG).n * 2 ^ (eval σ b σ ρG).n.toNat ≤ t.hi then
          some ((eval σ a σ ρG).n * 2 ^ (eval σ b σ ρG).n.toNat) else none)
       else some (cWrap t.w ((eval σ a σ ρG).n * 2 ^ (eval σ b σ ρG).n.toNat)))
      else none) = _
    rw [if_pos ⟨by omega, by omega, by omega⟩]
    have hr := htr.2
    cases hs : t.sgn with
    | true => rw [if_pos rfl, if_pos (by omega)]; rfl
    | false =>
        rw [if_neg (by decide)]
        have hh := CIT.hi_u hs
        rw [cWrap_of_range _ _ (by omega) (by unfold CIT.bits at hh; omega)]
        rfl)

/-- E16. `(a) >> (b)`. -/
theorem ecorr_shr (t : CIT) (w : Nat) {l1 h1 l2 h2 : Int} {ca cb : CX} (hw1 : h1 < 2 ^ w)
    (hw2 : h2 < (w : Int)) (h0 : 0 ≤ l1) (h0' : 0 ≤ l2)
    {a : Expr D Γ Λ (.int l1 h1)} {b : Expr D Γ Λ (.int l2 h2)}
    (ha : ExprCorr X K ca a) (hb : ExprCorr X K cb b) (hta : t.holds l1 h1) (htb : t.holds l2 h2)
    (hsh : h2 < (t.bits : Int)) :
    ExprCorr X K (.bin .shr t ca cb) (.shr w hw1 hw2 h0 h0' a b) :=
  ecorr_binop X K .shr t ha hb hta htb (fun σ ρG => by
    have ra := (eval σ a σ ρG).lo_le
    have rb := (eval σ b σ ρG).lo_le
    have rb' := (eval σ b σ ρG).le_hi
    show (if 0 ≤ (eval σ b σ ρG).n ∧ (eval σ b σ ρG).n < (t.bits : Int) ∧ 0 ≤ (eval σ a σ ρG).n
      then some ((eval σ a σ ρG).n / 2 ^ (eval σ b σ ρG).n.toNat) else none) = _
    rw [if_pos ⟨by omega, by omega, by omega⟩]
    rfl)

/-- The comparison scheme: operands in the comparison type, so C compares
    the Gabbro numbers (the signed/unsigned pitfall `-1 < 1u` is excluded
    by `hta`/`htb`). -/
theorem ecorr_cmp (op : CCmp) (t : CIT) {l1 h1 l2 h2 : Int} {ca cb : CX}
    {a : Expr D Γ Λ (.int l1 h1)} {b : Expr D Γ Λ (.int l2 h2)} {e : Expr D Γ Λ .bool}
    (ha : ExprCorr X K ca a) (hb : ExprCorr X K cb b) (hta : t.holds l1 h1) (htb : t.holds l2 h2)
    (hop : ∀ (σ : World D) (ρG : Env D Γ),
      op.app (eval σ a σ ρG).n (eval σ b σ ρG).n = wahr? (eval σ e σ ρG)) :
    ExprCorr X K (.cmp op t ca cb) e := by
  intro σ st ρG ρC hc he
  obtain ⟨st1, h1', hc1⟩ := ha.runI X K hc he
  obtain ⟨st2, h2', -⟩ := hb.runI X K hc1 he
  have ra := (eval σ a σ ρG).lo_le
  have ra' := (eval σ a σ ρG).le_hi
  have rb := (eval σ b σ ρG).lo_le
  have rb' := (eval σ b σ ρG).le_hi
  have ca' : conv t (eval σ a σ ρG).n = some (eval σ a σ ρG).n :=
    conv_id ⟨by have := hta.1; omega, by have := hta.2; omega⟩
  have cb' : conv t (eval σ b σ ρG).n = some (eval σ b σ ρG).n :=
    conv_id ⟨by have := htb.1; omega, by have := htb.2; omega⟩
  refine ⟨.int (b2i (wahr? (eval σ e σ ρG))), st2, ?_, ?_⟩
  · simp only [ev, h1', h2', ca', cb', hop σ ρG]
  · show CVal.int (b2i (wahr? (eval σ e σ ρG))) = .int (encW .bool (eval σ e σ ρG))
    rfl

/-- E17. `a < b`. -/
theorem ecorr_lt (t : CIT) {l1 h1 l2 h2 : Int} {ca cb : CX}
    {a : Expr D Γ Λ (.int l1 h1)} {b : Expr D Γ Λ (.int l2 h2)}
    (ha : ExprCorr X K ca a) (hb : ExprCorr X K cb b) (hta : t.holds l1 h1) (htb : t.holds l2 h2) :
    ExprCorr X K (.cmp .lt t ca cb) (.lt a b) :=
  ecorr_cmp X K .lt t ha hb hta htb (fun _ _ => rfl)

/-- E17. `a <= b`. -/
theorem ecorr_le (t : CIT) {l1 h1 l2 h2 : Int} {ca cb : CX}
    {a : Expr D Γ Λ (.int l1 h1)} {b : Expr D Γ Λ (.int l2 h2)}
    (ha : ExprCorr X K ca a) (hb : ExprCorr X K cb b) (hta : t.holds l1 h1) (htb : t.holds l2 h2) :
    ExprCorr X K (.cmp .le t ca cb) (.le a b) :=
  ecorr_cmp X K .le t ha hb hta htb (fun _ _ => rfl)

/-- E17. `a == b`. -/
theorem ecorr_eq (t : CIT) {l1 h1 l2 h2 : Int} {ca cb : CX}
    {a : Expr D Γ Λ (.int l1 h1)} {b : Expr D Γ Λ (.int l2 h2)}
    (ha : ExprCorr X K ca a) (hb : ExprCorr X K cb b) (hta : t.holds l1 h1) (htb : t.holds l2 h2) :
    ExprCorr X K (.cmp .eq t ca cb) (.eq a b) :=
  ecorr_cmp X K .eq t ha hb hta htb (fun _ _ => rfl)

/-- E17. `a > b` is Zucker.lean's `gt a b = lt b a`; C writes `a > b`. -/
theorem ecorr_gt (t : CIT) {l1 h1 l2 h2 : Int} {ca cb : CX}
    {a : Expr D Γ Λ (.int l1 h1)} {b : Expr D Γ Λ (.int l2 h2)}
    (ha : ExprCorr X K ca a) (hb : ExprCorr X K cb b) (hta : t.holds l1 h1) (htb : t.holds l2 h2) :
    ExprCorr X K (.cmp .gt t ca cb) (.lt b a) :=
  ecorr_cmp X K .gt t ha hb hta htb (fun _ _ => rfl)

/-- E18. `!(a)`. -/
theorem ecorr_nicht {c : CX} {a : Expr D Γ Λ .bool} (h : ExprCorr X K c a) :
    ExprCorr X K (.lnot c) (.nicht a) := by
  intro σ st ρG ρC hc he
  obtain ⟨st1, h1, -⟩ := h.runB X K hc he
  refine ⟨.int (b2i (!wahr? (eval σ a σ ρG))), st1, ?_, ?_⟩
  · simp only [ev, h1, truth_b2i]
  · show CVal.int (b2i (!wahr? (eval σ a σ ρG))) = .int (encW .bool (eval σ (Expr.nicht a) σ ρG))
    rfl

/-- The complement of a `w`-bit number is its xor with all ones. -/
theorem xor_allOnes (w x : Nat) (hx : x < 2 ^ w) : x ^^^ (2 ^ w - 1) = 2 ^ w - 1 - x := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one]
  have e : 2 ^ w - 1 - x = 2 ^ w - (x + 1) := by omega
  rw [e, Nat.testBit_two_pow_sub_succ hx]
  by_cases hi : i < w
  · simp [hi]
  · have hlt : x < 2 ^ i := Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega))
    simp [hi, Nat.testBit_lt_two_pow hlt]

/-- Evaluation rule of a cast. -/
theorem ev_cast {L : CLayout} {orc : DevOrc} {fr : Nat} {e : CX} {st : CSt} {ρ : CLok}
    {a : Int} {st1 : CSt} {b : Int} (t : CIT) (h : ev L orc fr e st ρ = some (.int a, st1))
    (hc : conv t a = some b) : ev L orc fr (.cast t e) st ρ = some (.int b, st1) := by
  simp only [ev, h, hc]

/-- Evaluation rule of `~`. -/
theorem ev_cpl {L : CLayout} {orc : DevOrc} {fr : Nat} {e : CX} {st : CSt} {ρ : CLok}
    {a : Int} {st1 : CSt} {a' : Int} (t : CIT) (h : ev L orc fr e st ρ = some (.int a, st1))
    (hc : conv t a = some a') :
    ev L orc fr (.cpl t e) st ρ = some (.int (if t.sgn then -a' - 1 else t.hi - a'), st1) := by
  simp only [ev, h, hc]

/-- `-x - 1` into an unsigned type of `n` bits is `2^n - 1 - x`. -/
theorem conv_negU {t : CIT} (hs : t.sgn = false) (x : Int) (h0 : 0 ≤ x) (h1 : x < 2 ^ t.bits) :
    conv t (-x - 1) = some (2 ^ t.bits - 1 - x) := by
  have hp := two_pow_pos' t.bits
  have hlo := CIT.lo_u hs
  unfold conv
  rw [if_neg (by omega), if_neg (by rw [hs]; decide)]
  congr 1
  show ((-x - 1) % 2 ^ t.bits + 2 ^ t.bits) % 2 ^ t.bits = 2 ^ t.bits - 1 - x
  have e1 : -x - 1 = (2 ^ t.bits - 1 - x) + (-1) * 2 ^ t.bits := by omega
  have e2 : (2 ^ t.bits - 1 - x) + 2 ^ t.bits = (2 ^ t.bits - 1 - x) + 1 * 2 ^ t.bits := by omega
  have i1 : (-x - 1) % 2 ^ t.bits = 2 ^ t.bits - 1 - x := by
    rw [e1, Int.add_mul_emod_self_right]; exact Int.emod_eq_of_lt (by omega) (by omega)
  have i2 : (2 ^ t.bits - 1 - x + 2 ^ t.bits) % 2 ^ t.bits = 2 ^ t.bits - 1 - x := by
    rw [e2, Int.add_mul_emod_self_right]; exact Int.emod_eq_of_lt (by omega) (by omega)
  rw [i1, i2]

/-- E19. `(T)~(T)(x)` for an unsigned `T` of `w` bits is Zucker.lean's
    `~a = a ^ (2^w - 1)`, both where `~` computes in `int` (`uint8_t`,
    `uint16_t`: `-x - 1` wrapped back) and where it computes in `T`
    itself (`2^w - 1 - x`). -/
theorem ecorr_bnot (t : CIT) (hts : t.sgn = false) {l1 h1 : Int} {cx : CX}
    (h0 : 0 ≤ l1) (hw : h1 < 2 ^ t.bits) {a : Expr D Γ Λ (.int l1 h1)}
    (ha : ExprCorr X K cx a) (hta : t.holds l1 h1) :
    ExprCorr X K (.cast t (.cpl t.promote (.cast t cx))) (Expr.bnot t.bits h0 hw a) := by
  intro σ st ρG ρC hc he
  obtain ⟨st1, h1', -⟩ := ha.runI X K hc he
  have ra := (eval σ a σ ρG).lo_le
  have ra' := (eval σ a σ ρG).le_hi
  have hp := two_pow_pos' t.bits
  have hhi := CIT.hi_u hts
  have hlo := CIT.lo_u hts
  have hx0 : 0 ≤ (eval σ a σ ρG).n := by omega
  have hx1 : (eval σ a σ ρG).n < 2 ^ t.bits := by omega
  have c1 : conv t (eval σ a σ ρG).n = some (eval σ a σ ρG).n := conv_id ⟨by omega, by omega⟩
  have e1 := ev_cast t h1' c1
  have hres : ev X.EL.lay X.orc X.fr (.cast t (.cpl t.promote (.cast t cx))) st ρC =
      some (.int (2 ^ t.bits - 1 - (eval σ a σ ρG).n), st1) := by
    rcases t with ⟨sgn, w⟩
    cases hts
    have i32lo : CIT.i32.lo = -2147483648 := by decide
    have i32hi : CIT.i32.hi = 2147483647 := by decide
    cases w with
    | w8 =>
        have hb : (2 : Int) ^ CIT.bits ⟨false, .w8⟩ = 256 := by decide
        have c2 : conv CIT.i32 (eval σ a σ ρG).n = some (eval σ a σ ρG).n :=
          conv_id ⟨by omega, by omega⟩
        have e2 : ev X.EL.lay X.orc X.fr (.cpl CIT.i32 (.cast ⟨false, .w8⟩ cx)) st ρC =
            some (.int (-(eval σ a σ ρG).n - 1), st1) := by
          rw [ev_cpl CIT.i32 e1 c2]; rfl
        exact ev_cast _ e2 (conv_negU rfl _ hx0 hx1)
    | w16 =>
        have hb : (2 : Int) ^ CIT.bits ⟨false, .w16⟩ = 65536 := by decide
        have c2 : conv CIT.i32 (eval σ a σ ρG).n = some (eval σ a σ ρG).n :=
          conv_id ⟨by omega, by omega⟩
        have e2 : ev X.EL.lay X.orc X.fr (.cpl CIT.i32 (.cast ⟨false, .w16⟩ cx)) st ρC =
            some (.int (-(eval σ a σ ρG).n - 1), st1) := by
          rw [ev_cpl CIT.i32 e1 c2]; rfl
        exact ev_cast _ e2 (conv_negU rfl _ hx0 hx1)
    | w32 =>
        have e2 := ev_cpl ⟨false, .w32⟩ e1 c1
        have v2 : (if (⟨false, .w32⟩ : CIT).sgn = true then -(eval σ a σ ρG).n - 1
            else CIT.hi ⟨false, .w32⟩ - (eval σ a σ ρG).n) =
            2 ^ CIT.bits ⟨false, .w32⟩ - 1 - (eval σ a σ ρG).n := by
          rw [if_neg (by decide), hhi]
        rw [v2] at e2
        exact ev_cast _ e2 (conv_id ⟨by omega, by omega⟩)
    | w64 =>
        have e2 := ev_cpl ⟨false, .w64⟩ e1 c1
        have v2 : (if (⟨false, .w64⟩ : CIT).sgn = true then -(eval σ a σ ρG).n - 1
            else CIT.hi ⟨false, .w64⟩ - (eval σ a σ ρG).n) =
            2 ^ CIT.bits ⟨false, .w64⟩ - 1 - (eval σ a σ ρG).n := by
          rw [if_neg (by decide), hhi]
        rw [v2] at e2
        exact ev_cast _ e2 (conv_id ⟨by omega, by omega⟩)
  refine ⟨_, st1, hres, ?_⟩
  show CVal.int (2 ^ t.bits - 1 - (eval σ a σ ρG).n) =
    .int ((((eval σ a σ ρG).n.toNat ^^^ (2 ^ t.bits - 1 : Int).toNat : Nat) : Int))
  congr 1
  have ep : ((2 ^ t.bits : Nat) : Int) = (2 : Int) ^ t.bits := by simp
  have e1' : (2 ^ t.bits - 1 : Int).toNat = 2 ^ t.bits - 1 := by omega
  have hxn : (eval σ a σ ρG).n.toNat < 2 ^ t.bits := by omega
  rw [e1', xor_allOnes _ _ hxn]
  have : 1 ≤ 2 ^ t.bits := Nat.one_le_two_pow
  omega

/-- E20. `(T)(e)` as `verenge` writes it: only where the value provably
    fits `T` (12052), so the cast keeps it. -/
theorem ecorr_cast (t : CIT) {lo hi : Int} {c : CX} {e : Expr D Γ Λ (.int lo hi)}
    (h : ExprCorr X K c e) (ht : t.holds lo hi) : ExprCorr X K (.cast t c) e := by
  intro σ st ρG ρC hc he
  obtain ⟨st1, h1, -⟩ := h.runI X K hc he
  have r1 := (eval σ e σ ρG).lo_le
  have r2 := (eval σ e σ ρG).le_hi
  exact ⟨_, st1, ev_cast t h1 (conv_id ⟨by have := ht.1; omega, by have := ht.2; omega⟩), rfl⟩

/-- A cell type that holds a Gabbro type makes the encoded value the
    corresponding C value. -/
theorem valCorr_encW {EL : EmitLay D} (τ : Ty) (c : CTy) (v : Wert D τ) (hf : tyFits τ c = true) :
    ValCorr EL τ v (.int (encW τ v)) := by
  cases τ with
  | int lo hi => rfl
  | bool => rfl
  | opt n => rfl
  | grund n => rfl
  | sum cs => exact absurd hf (by cases c <;> simp [tyFits])
  | never => exact absurd hf (by cases c <;> simp [tyFits])
  | fl lo hi => exact absurd hf (by cases c <;> simp [tyFits])
  | fnptr s => exact absurd hf (by cases c <;> simp [tyFits])
  | ptr t rw => exact absurd hf (by cases c <;> simp [tyFits])

theorem valCorr_int_of_fits {EL : EmitLay D} (τ : Ty) (c : CTy) (w : Wert D τ) (v : CVal)
    (hf : tyFits τ c = true) (h : ValCorr EL τ w v) : v = .int (encW τ w) := by
  cases τ with
  | int lo hi => exact h
  | bool => exact h
  | opt n => exact h
  | grund n => exact h
  | sum cs => exact absurd hf (by cases c <;> simp [tyFits])
  | never => exact absurd hf (by cases c <;> simp [tyFits])
  | fl lo hi => exact absurd hf (by cases c <;> simp [tyFits])
  | fnptr s => exact absurd hf (by cases c <;> simp [tyFits])
  | ptr t rw => exact absurd hf (by cases c <;> simp [tyFits])

theorem convV_of_valFits (c : CTy) (n : Int) (h : valFits c (.int n) = true) :
    convV c (.int n) = some (.int n) := by
  cases c with
  | ptr => simp [valFits] at h
  | int s w =>
      simp only [valFits, decide_eq_true_eq] at h
      simp only [convV]
      rw [conv_id (t := ⟨s, w⟩) h]

/-- The slot address of the named table: `T_speicher.slots[k].f` is the
    emitted slot pointer of `EmitLay`. -/
theorem ptrAdd_slot (EL : EmitLay D) (t : D.Tab) (f : D.Feld t) (k : Int) (k0 : 0 ≤ k)
    (k1 : k < D.count t) :
    ptrAdd EL.lay ⟨.tab (EL.tnr t), 0⟩
      (k * ((EL.trec t).ssize : Int) + ((EL.trec t).off (EL.fnr t f) : Int)) 1 =
      some (EL.slotPtr t k f) := by
  have hcnt := EL.trec_count t
  have hk' : k.toNat < (EL.trec t).count := by omega
  have hoff := RecLay.off_lt (EL.trec_wf t) (EL.fnr_lt t f)
  have hnat : k.toNat * (EL.trec t).ssize + (EL.trec t).off (EL.fnr t f) ≤
      (EL.trec t).count * (EL.trec t).ssize := by
    have := Nat.mul_le_mul_right (EL.trec t).ssize hk'
    rw [Nat.succ_mul] at this
    omega
  have hint : k * ((EL.trec t).ssize : Int) + ((EL.trec t).off (EL.fnr t f) : Int) =
      ((k.toNat * (EL.trec t).ssize + (EL.trec t).off (EL.fnr t f) : Nat) : Int) := by
    rw [Int.natCast_add, Int.natCast_mul, Int.toNat_of_nonneg k0]
  have e1 : (⟨.tab (EL.tnr t), 0⟩ : CPtr).off +
      (k * ((EL.trec t).ssize : Int) + ((EL.trec t).off (EL.fnr t f) : Int)) * ((1 : Nat) : Int) =
      ((k.toNat * (EL.trec t).ssize + (EL.trec t).off (EL.fnr t f) : Nat) : Int) := by
    show (0 : Int) + _ * ((1 : Nat) : Int) = _
    rw [Int.natCast_one, Int.mul_one, Int.zero_add, hint]
  rw [ptrAdd_progress EL.lay ⟨.tab (EL.tnr t), 0⟩ _ 1 _ (EL.lay_tab t) (by rw [e1]; omega)
    (by
      rw [e1]
      show _ ≤ (((EL.trec t).count * (EL.trec t).ssize : Nat) : Int)
      omega)]
  rw [e1]
  rfl

/-- E23. `T_speicher.slots[i].f` (a table named directly): the emitted
    slot load reads the encoded slot. -/
theorem ecorr_slotNamed (t : D.Tab) (f : D.Feld t) (hgt : D.geist t = false) {ci : CX}
    {i : Expr D Γ Λ (.index (D.count t))} (hL : darf D t Λ) (hi : ExprCorr X K ci i) :
    ExprCorr X K (.ld (.slotA (.addr (.tab (X.EL.tnr t))) ci (X.EL.trec t).count
      (X.EL.trec t).ssize ((X.EL.trec t).off (X.EL.fnr t f))) (X.EL.slotTy t f))
      (Expr.slot t f i hL) := by
  intro σ st ρG ρC hc he
  obtain ⟨st1, h1, hc1⟩ := hi.runI X K hc he
  have k0 := (eval σ i σ ρG).lo_le
  have k1 := (eval σ i σ ρG).le_hi
  have hcnt := X.EL.trec_count t
  have hp := ptrAdd_slot X.EL t f (eval σ i σ ρG).n k0 (by omega)
  have hl := corr_leseSlot X.EL σ st1 hc1 t hgt (eval σ i σ ρG).n f k0 (by omega)
  refine ⟨.int (encW (D.typ t f) (σ.slots t (eval σ i σ ρG).n f)), st1, ?_,
    valCorr_encW _ _ _ (X.EL.fnr_fits t f)⟩
  have hb : 0 ≤ (eval σ i σ ρG).n ∧ (eval σ i σ ρG).n < ((X.EL.trec t).count : Int) :=
    ⟨k0, by omega⟩
  simp only [ev, h1, if_pos hb, hp, hl]

/-- E24. A plain file-scope scalar `g`. -/
theorem ecorr_glob (g : D.Glob) (hgg : D.ggeist g = false) (hat : D.atomar g = false)
    (hL : gdarf D g Λ) :
    ExprCorr X K (.ld (.addr (.glob (X.EL.gnr g))) (X.EL.gty g))
      (Expr.glob (Γ := Γ) g hL) := by
  intro σ st ρG ρC hc _
  refine ⟨.int (encW (D.gtyp g) (σ.globs g)), st, ?_, valCorr_encW _ _ _ (X.EL.gty_fits g)⟩
  have hl := corr_leseGlob X.EL σ st hc g hgg hat
  simp only [ev]
  rw [show (⟨.glob (X.EL.gnr g), 0⟩ : CPtr) = X.EL.globPtr g from rfl, hl]

/-- E25. A bare `_Atomic` name `g` in an expression: C11 makes it a
    `seq_cst` atomic load (the emitter writes the bare name, 12804ff.; the
    explicit calls are for `publishes`/`awaits`/`exchange`). The load
    appends its observation. -/
theorem ecorr_globAtomar (g : D.Glob) (hgg : D.ggeist g = false) (hat : D.atomar g = true)
    (hL : gdarf D g Λ) :
    ExprCorr X K (.ald (.addr (.glob (X.EL.gnr g))) (X.EL.gty g) .seqCst)
      (Expr.glob (Γ := Γ) g hL) := by
  intro σ st ρG ρC hc _
  refine ⟨.int (encW (D.gtyp g) (σ.globs g)),
    { st with obs := .ard (X.EL.globPtr g) .seqCst (encW (D.gtyp g) (σ.globs g)) :: st.obs },
    ?_, valCorr_encW _ _ _ (X.EL.gty_fits g)⟩
  have hl := corr_leseGlob_atomar X.EL σ st hc g hgg hat .seqCst rfl
  simp only [ev]
  rw [show (⟨.glob (X.EL.gnr g), 0⟩ : CPtr) = X.EL.globPtr g from rfl, hl]

end Ausdruck

/-! ## 4. Pass (i): statements -/

/-- A C declaration type holds a Gabbro type: an integer cell type that
    holds its range (`tyFits`), or a pointer for a pointer. -/
def declOk : Ty → CTy → Bool
  | .ptr _ _, .ptr => true
  | .ptr _ _, _ => false
  | τ, c => tyFits τ c

theorem convV_of_valCorr {EL : EmitLay D} {τ : Ty} {v : Wert D τ} {c : CVal} {τc : CTy}
    (h : ValCorr EL τ v c) (hd : declOk τ τc = true) : convV τc c = some c := by
  cases τ with
  | ptr n rw =>
      obtain ⟨t, -, hc⟩ := h
      subst hc
      cases τc with
      | ptr => rfl
      | int s w => simp [declOk] at hd
  | int lo hi =>
      have hc : c = .int (encW (.int lo hi) v) := h
      subst hc
      exact convV_of_valFits _ _ (encW_fits _ _ v hd)
  | bool =>
      have hc : c = .int (encW .bool v) := h
      subst hc
      exact convV_of_valFits _ _ (encW_fits _ _ v hd)
  | opt n =>
      have hc : c = .int (encW (.opt n) v) := h
      subst hc
      exact convV_of_valFits _ _ (encW_fits _ _ v hd)
  | grund n =>
      have hc : c = .int (encW (.grund n) v) := h
      subst hc
      exact convV_of_valFits _ _ (encW_fits _ _ v hd)
  | sum cs => exact h.elim
  | never => exact h.elim
  | fl lo hi => exact h.elim
  | fnptr s => exact h.elim

section Anweisung

variable (X : TVCtx D) (m : Nat) {Γ : Ctx} (K : CEnvLay D Γ) {V : Vertrag D} {l : Bool}
  {Λ : List (Res D)}

/-- S1. `x = e;` on a local. -/
theorem scorr_assignVar (hK : K.okB = true) {τ : Ty} (x : Var Γ τ) {e : Expr D Γ Λ τ}
    {ce : CX} {τc : CTy} (he : ExprCorr X K ce e) (hd : declOk τ τc = true) :
    StmtCorr X m K (Stmt.assignVar (V := V) (l := l) x e) (.set (K.loc x) τc ce) := by
  intro σ st ρG ρC hc hr _
  have hc' : corrW X.EL (σ.lese Λ e.orte) st := (corrW_lese _ _ _ _ _).mpr hc
  obtain ⟨v, st1, hev, hv, hc1⟩ := he.run X K hc' hr
  refine ⟨.norm st1 (lokUpd ρC (K.loc x) v), Exec.set hev (convV_of_valCorr hv hd), ?_⟩
  exact ⟨st1, _, rfl, hc1, envRel_set hK hr x _ v hv⟩

/-- S2. `x += e;` (C11 6.5.16.2p3: `x = x + (e)` with `x` evaluated
    once) is Zucker.lean's `plusGleich`. -/
theorem scorr_plusGleich (hK : K.okB = true) {lo hi lo' hi' : Int} (x : Var Γ (.int lo hi))
    {e : Expr D Γ Λ (.int lo' hi')} {ce : CX} (t : CIT) {τc : CTy}
    (h1 : lo ≤ lo + lo') (h2 : hi + hi' ≤ hi) (he : ExprCorr X K ce e)
    (hta : t.holds lo hi) (htb : t.holds lo' hi') (htr : t.holds (lo + lo') (hi + hi'))
    (hd : declOk (.int lo hi) τc = true) :
    StmtCorr X m K (Stmt.plusGleich (V := V) (l := l) x e h1 h2)
      (.set (K.loc x) τc (.bin .add t (.var (K.loc x)) ce)) :=
  scorr_assignVar X m K hK x
    (ecorr_weiter X K h1 h2 (ecorr_add X K t (ecorr_var X K x) he hta htb htr)) hd

/-- S2. `x -= e;` -/
theorem scorr_minusGleich (hK : K.okB = true) {lo hi lo' hi' : Int} (x : Var Γ (.int lo hi))
    {e : Expr D Γ Λ (.int lo' hi')} {ce : CX} (t : CIT) {τc : CTy}
    (h1 : lo ≤ lo - hi') (h2 : hi - lo' ≤ hi) (he : ExprCorr X K ce e)
    (hta : t.holds lo hi) (htb : t.holds lo' hi') (htr : t.holds (lo - hi') (hi - lo'))
    (hd : declOk (.int lo hi) τc = true) :
    StmtCorr X m K (Stmt.minusGleich (V := V) (l := l) x e h1 h2)
      (.set (K.loc x) τc (.bin .sub t (.var (K.loc x)) ce)) :=
  scorr_assignVar X m K hK x
    (ecorr_weiter X K h1 h2 (ecorr_sub X K t (ecorr_var X K x) he hta htb htr)) hd

/-- S2. `x &= e;` over `0 ..`. -/
theorem scorr_undGleich (hK : K.okB = true) {hi lo' hi' : Int} (x : Var Γ (.int 0 hi))
    {e : Expr D Γ Λ (.int lo' hi')} {ce : CX} (t : CIT) {τc : CTy} (h0' : 0 ≤ lo')
    (he : ExprCorr X K ce e) (hta : t.holds 0 hi) (htb : t.holds lo' hi')
    (hd : declOk (.int 0 hi) τc = true) :
    StmtCorr X m K (Stmt.undGleich (V := V) (l := l) x e h0')
      (.set (K.loc x) τc (.bin .band t (.var (K.loc x)) ce)) :=
  scorr_assignVar X m K hK x (ecorr_band X K t _ h0' (ecorr_var X K x) he hta htb) hd

/-- S2. `x |= e;` in width `w`. -/
theorem scorr_oderGleich (hK : K.okB = true) (w : Nat) {lo' hi' : Int}
    (x : Var Γ (.int 0 (2 ^ w - 1))) {e : Expr D Γ Λ (.int lo' hi')} {ce : CX} (t : CIT)
    {τc : CTy} (h0' : 0 ≤ lo') (hw : hi' < 2 ^ w) (he : ExprCorr X K ce e)
    (hta : t.holds 0 (2 ^ w - 1)) (htb : t.holds lo' hi')
    (hd : declOk (.int 0 (2 ^ w - 1)) τc = true) :
    StmtCorr X m K (Stmt.oderGleich (V := V) (l := l) w x e h0' hw)
      (.set (K.loc x) τc (.bin .bor t (.var (K.loc x)) ce)) :=
  scorr_assignVar X m K hK x (ecorr_bor X K t w _ h0' _ hw (ecorr_var X K x) he hta htb) hd

/-- S3. `T_speicher.slots[i].f = e;` -- the store of `corr_schreibSlot`,
    reached through the emitted address computation. -/
theorem scorr_assignSlotNamed (t : D.Tab) (f : D.Feld t) (hgt : D.geist t = false)
    {i : Expr D Γ Λ (.index (D.count t))} {e : Expr D Γ Λ (D.typ t f)} {ci ce : CX}
    (hw : V.schreibt t = true) (hL : darf D t Λ) (hi : ExprCorr X K ci i)
    (he : ExprCorr X K ce e) :
    StmtCorr X m K (Stmt.assignSlot (l := l) t f i e hw hL)
      (.store (.slotA (.addr (.tab (X.EL.tnr t))) ci (X.EL.trec t).count (X.EL.trec t).ssize
        ((X.EL.trec t).off (X.EL.fnr t f))) (X.EL.slotTy t f) ce) := by
  intro σ st ρG ρC hc hr _
  have hc' : corrW X.EL (σ.lese Λ (i.orte ++ e.orte)) st := (corrW_lese _ _ _ _ _).mpr hc
  obtain ⟨st1, h1, hc1⟩ := hi.runI X K hc' hr
  obtain ⟨v, st2, h2, hv, hc2⟩ := he.run X K hc1 hr
  have k0 := (eval (σ.lese Λ (i.orte ++ e.orte)) i (σ.lese Λ (i.orte ++ e.orte)) ρG).lo_le
  have k1 := (eval (σ.lese Λ (i.orte ++ e.orte)) i (σ.lese Λ (i.orte ++ e.orte)) ρG).le_hi
  have hcnt := X.EL.trec_count t
  have hp := ptrAdd_slot X.EL t f
    (eval (σ.lese Λ (i.orte ++ e.orte)) i (σ.lese Λ (i.orte ++ e.orte)) ρG).n k0 (by omega)
  have hb : 0 ≤ (eval (σ.lese Λ (i.orte ++ e.orte)) i (σ.lese Λ (i.orte ++ e.orte)) ρG).n ∧
      (eval (σ.lese Λ (i.orte ++ e.orte)) i (σ.lese Λ (i.orte ++ e.orte)) ρG).n <
        ((X.EL.trec t).count : Int) := ⟨k0, by omega⟩
  have hav : ev X.EL.lay X.orc X.fr (.slotA (.addr (.tab (X.EL.tnr t))) ci (X.EL.trec t).count
      (X.EL.trec t).ssize ((X.EL.trec t).off (X.EL.fnr t f))) st ρC =
      some (.ptr (X.EL.slotPtr t
        (eval (σ.lese Λ (i.orte ++ e.orte)) i (σ.lese Λ (i.orte ++ e.orte)) ρG).n f), st1) := by
    simp only [ev, h1, if_pos hb, hp]
  have hve := valCorr_int_of_fits _ _ _ _ (X.EL.fnr_fits t f) hv
  subst hve
  obtain ⟨st3, hs, hc3, -⟩ := corr_schreibSlot X.EL (σ.lese Λ (i.orte ++ e.orte)) st2 hc2 t hgt Λ
    (eval (σ.lese Λ (i.orte ++ e.orte)) i (σ.lese Λ (i.orte ++ e.orte)) ρG).n f
    (eval (σ.lese Λ (i.orte ++ e.orte)) e (σ.lese Λ (i.orte ++ e.orte)) ρG) k0 (by omega)
  refine ⟨.norm st3 ρC, Exec.store hav h2
    (convV_of_valFits _ _ (encW_fits _ _ _ (X.EL.fnr_fits t f))) hs, ?_⟩
  exact ⟨st3, ρC, rfl, hc3, hr⟩

/-- S4. `g = e;` on a plain file-scope scalar. -/
theorem scorr_assignGlob (g : D.Glob) (hgg : D.ggeist g = false) (hat : D.atomar g = false)
    {e : Expr D Γ Λ (D.gtyp g)} {ce : CX} (hw : V.gschreibt g = true) (hL : gdarf D g Λ)
    (he : ExprCorr X K ce e) :
    StmtCorr X m K (Stmt.assignGlob (l := l) g e hw hL)
      (.store (.addr (.glob (X.EL.gnr g))) (X.EL.gty g) ce) := by
  intro σ st ρG ρC hc hr _
  have hc' : corrW X.EL (σ.lese Λ e.orte) st := (corrW_lese _ _ _ _ _).mpr hc
  obtain ⟨v, st1, h1, hv, hc1⟩ := he.run X K hc' hr
  have hve := valCorr_int_of_fits _ _ _ _ (X.EL.gty_fits g) hv
  subst hve
  obtain ⟨st2, hs, hc2, -⟩ := corr_schreibGlob X.EL _ st1 hc1 g hgg hat Λ
    (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρG)
  refine ⟨.norm st2 ρC, Exec.store (by simp only [ev]; rfl) h1
    (convV_of_valFits _ _ (encW_fits _ _ _ (X.EL.gty_fits g))) hs, ?_⟩
  exact ⟨st2, ρC, rfl, hc2, hr⟩

/-- S4. `g = e;` on an `_Atomic` global: a `seq_cst` atomic store, one
    observation (the emitter writes the bare name). -/
theorem scorr_assignGlobAtomar (g : D.Glob) (hgg : D.ggeist g = false)
    (hat : D.atomar g = true) {e : Expr D Γ Λ (D.gtyp g)} {ce : CX}
    (hw : V.gschreibt g = true) (hL : gdarf D g Λ) (he : ExprCorr X K ce e) :
    StmtCorr X m K (Stmt.assignGlob (l := l) g e hw hL)
      (.astore (.addr (.glob (X.EL.gnr g))) (X.EL.gty g) .seqCst ce) := by
  intro σ st ρG ρC hc hr _
  have hc' : corrW X.EL (σ.lese Λ e.orte) st := (corrW_lese _ _ _ _ _).mpr hc
  obtain ⟨v, st1, h1, hv, hc1⟩ := he.run X K hc' hr
  have hve := valCorr_int_of_fits _ _ _ _ (X.EL.gty_fits g) hv
  subst hve
  obtain ⟨st2, hs, hc2, -⟩ := corr_schreibGlob_atomar X.EL _ st1 hc1 g hgg hat Λ
    (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρG) .seqCst rfl
  refine ⟨.norm st2 ρC, Exec.astore (by simp only [ev]; rfl) h1
    (convV_of_valFits _ _ (encW_fits _ _ _ (X.EL.gty_fits g))) hs, ?_⟩
  exact ⟨st2, ρC, rfl, hc2, hr⟩

/-- The C side of an answer: none for `return;`, a corresponding
    expression at a fitting return type for `return e;`. -/
def ErgCorr {Γ : Ctx} {Λ : List (Res D)} (K : CEnvLay D Γ) :
    {e : Option Ty} → ErgExpr D Γ Λ e → Option (CTy × CX) → Prop
  | _, .keine, cr => cr = none
  | some τ, .wert e, cr => ∃ τc ce, cr = some (τc, ce) ∧ ExprCorr X K ce e ∧ declOk τ τc = true

/-- Running the C side of an answer. -/
theorem ergCorr_run {r : ErgExpr D Γ Λ V.erg} {cr : Option (CTy × CX)} (h : ErgCorr X K r cr)
    {σ : World D} {st : CSt} {ρG : Env D Γ} {ρC : CLok} (hc : corrW X.EL σ st)
    (hr : EnvRel X.EL K ρG ρC) :
    ∃ st' cv, Exec X.EL.lay X.orc X.fr X.CR X.XR (.ret cr) st ρC (.ret st' cv) ∧
      corrW X.EL σ st' ∧ RetCorr X.EL V.erg (evalErg σ r σ ρG) cv := by
  revert h
  generalize V.erg = eg at r
  intro h
  cases r with
  | keine =>
      have hcr : cr = none := h
      subst hcr
      exact ⟨st, none, Exec.retN, hc, rfl⟩
  | wert e =>
      obtain ⟨τc, ce, hcr, he, hd⟩ := h
      subst hcr
      obtain ⟨v, st1, h1, hv, hc1⟩ := he.run X K hc hr
      exact ⟨st1, some v, Exec.retS h1 (convV_of_valCorr hv hd), hc1, v, rfl, hv⟩

/-- S5. `return e;` / `return;`. -/
theorem scorr_ret {r : ErgExpr D Γ Λ V.erg} {cr : Option (CTy × CX)} (hΛ : Λ.Perm V.ende)
    (h : ErgCorr X K r cr) :
    StmtCorr X m K (Stmt.ret (l := l) r hΛ) (.ret cr) := by
  intro σ st ρG ρC hc hr _
  have hc' : corrW X.EL (σ.lese Λ r.orte) st := (corrW_lese _ _ _ _ _).mpr hc
  obtain ⟨st', cv, he, hc1, hrc⟩ := ergCorr_run X K h hc' hr
  exact ⟨_, he, st', cv, rfl, hc1, hrc⟩

/-- S6. `if (c) { … } else { … }`: the arms correspond as blocks. -/
theorem scorr_ite {Λ' : List (Res D)} {c : Expr D Γ Λ .bool} {t e : Block D V l Γ Λ Λ'}
    {cc : CX} {ct ce : CS} (hc : ExprCorr X K cc c) (ht : BlockSem X m K t ct)
    (he : BlockSem X m K e ce) :
    StmtCorr X m K (Stmt.ite c t e) (.ite cc ct ce) := by
  intro σ st ρG ρC hcw hr hnf
  have hc' : corrW X.EL (σ.lese Λ c.orte) st := (corrW_lese _ _ _ _ _).mpr hcw
  obtain ⟨st1, h1, hc1⟩ := hc.runB X K hc' hr
  have hex : execStmt X.O X.passes X.R (Stmt.ite c t e) σ ρG =
      if wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρG) then
        execBlock X.O X.passes X.R t (σ.lese Λ c.orte) ρG
      else execBlock X.O X.passes X.R e (σ.lese Λ c.orte) ρG := rfl
  rw [hex] at hnf ⊢
  by_cases hb : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρG) = true
  · rw [if_pos hb] at hnf ⊢
    rw [hb] at h1
    obtain ⟨o, hx, ho⟩ := ht _ st1 ρG ρC hc1 hr hnf
    exact ⟨o, Exec.iteT h1 (truth_b2i true) hx, ho⟩
  · rw [if_neg hb] at hnf ⊢
    have hb' : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρG) = false := by
      cases h' : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρG)
      · rfl
      · exact absurd h' hb
    rw [hb'] at h1
    obtain ⟨o, hx, ho⟩ := he _ st1 ρG ρC hc1 hr hnf
    exact ⟨o, Exec.iteF h1 (truth_b2i false) hx, ho⟩

end Anweisung

/-! ## 5. Blocks: `cCorr_block` -/

/-- Leaving a `let`'s scope drops its variable from the relation. -/
theorem envRel_pop {EL : EmitLay D} {Γ : Ctx} {K : CEnvLay D Γ} {τ : Ty} {x : Nat}
    {ρG : Env D (τ :: Γ)} {ρC : CLok} (h : EnvRel EL (K.push τ x) ρG ρC) :
    EnvRel EL K ρG.tail ρC := by
  cases ρG with
  | cons v ρ =>
      refine ⟨fun τ' y => h.1 τ' (.dort y), h.2.1, h.2.2⟩

theorem istFehler_schrumpf {V : Vertrag D} {l : Bool} {Γ : Ctx} {τ : Ty}
    (a : Ausgang V l (τ :: Γ)) : a.schrumpf.istFehler = a.istFehler := by
  cases a <;> rfl

theorem stOut_schrumpf (X : TVCtx D) (m : Nat) {Γ : Ctx} {K : CEnvLay D Γ} {τ : Ty} {x : Nat}
    {V : Vertrag D} {l : Bool} (a : Ausgang V l (τ :: Γ)) (o : COut)
    (h : StOut X m (K.push τ x) a o) : StOut X m K a.schrumpf o := by
  cases a with
  | ok σ ρ =>
      obtain ⟨st', ρC', ho, hc, hr⟩ := h
      exact ⟨st', ρC', ho, hc, envRel_pop hr⟩
  | zurueck σ v => exact h
  | grund σ r => exact h.elim
  | leave hl σ ρ =>
      obtain ⟨st', ρC', ho, hc, hr⟩ := h
      exact ⟨st', ρC', ho, hc, envRel_pop hr⟩
  | next hl σ ρ =>
      obtain ⟨st', ρC', ho, hc, hr⟩ := h
      exact ⟨st', ρC', ho, hc, envRel_pop hr⟩
  | logik e => exact h.elim
  | hardware e => exact h.elim

/-- THE BLOCK CORRESPONDENCE, as the certificate states it: statement by
    statement, each `let` into a fresh C local of a fitting type, and the
    C-only statements `(void)x;` (an expression evaluated for nothing,
    `pre`). -/
inductive BlockCorr (X : TVCtx D) (m : Nat) {V : Vertrag D} {l : Bool} :
    {Γ : Ctx} → {Λ Λ' : List (Res D)} → CEnvLay D Γ → Block D V l Γ Λ Λ' → CS → Prop where
  | nil {Γ : Ctx} {Λ : List (Res D)} {K : CEnvLay D Γ} :
      BlockCorr X m K (Block.nil (Λ := Λ)) .skip
  | cons {Γ : Ctx} {Λ Λ' Λ'' : List (Res D)} {K : CEnvLay D Γ} {s : Stmt D V l Γ Λ Λ'}
      {rest : Block D V l Γ Λ' Λ''} {cs cr : CS} (hs : StmtCorr X m K s cs)
      (hr : BlockCorr X m K rest cr) : BlockCorr X m K (.cons s rest) (.seq cs cr)
  | bind {Γ : Ctx} {Λ Λ' : List (Res D)} {K : CEnvLay D Γ} {τ : Ty} {e : Expr D Γ Λ τ}
      {rest : Block D V l (τ :: Γ) Λ Λ'} {x : Nat} {τc : CTy} {ce : CX} {cr : CS}
      (hK : K.okB = true) (hf : K.freshB x = true) (he : ExprCorr X K ce e)
      (hd : declOk τ τc = true) (hr : BlockCorr X m (K.push τ x) rest cr) :
      BlockCorr X m K (.bind e rest) (.seq (.set x τc ce) cr)
  | pre {Γ : Ctx} {Λ Λ' Λ0 : List (Res D)} {K : CEnvLay D Γ} {b : Block D V l Γ Λ Λ'}
      {τ0 : Ty} {e0 : Expr D Γ Λ0 τ0} {ce : CX} {cr : CS} (he : ExprCorr X K ce e0)
      (hr : BlockCorr X m K b cr) : BlockCorr X m K b (.seq (.expr ce) cr)

/-- Running a C-only `(void)e;`: nothing related changes. -/
theorem pre_run {X : TVCtx D} {Γ : Ctx} {Λ0 : List (Res D)} {K : CEnvLay D Γ} {τ0 : Ty}
    {e0 : Expr D Γ Λ0 τ0} {ce : CX} (he : ExprCorr X K ce e0) {σ : World D} {st : CSt}
    {ρG : Env D Γ} {ρC : CLok} (hc : corrW X.EL σ st) (hr : EnvRel X.EL K ρG ρC) :
    ∃ st1, Exec X.EL.lay X.orc X.fr X.CR X.XR (.expr ce) st ρC (.norm st1 ρC) ∧
      corrW X.EL σ st1 := by
  obtain ⟨v, st1, h1, -, hc1⟩ := he.run X K hc hr
  exact ⟨st1, Exec.expr h1, hc1⟩

/-- THE BLOCK THEOREM: if every statement of a Gabbro block corresponds
    to its emitted C statement (and every `let` to its declaration), the
    emitted block corresponds to the Gabbro block. -/
theorem cCorr_block (X : TVCtx D) (m : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {K : CEnvLay D Γ} {b : Block D V l Γ Λ Λ'} {cb : CS}
    (h : BlockCorr X m K b cb) : BlockSem X m K b cb := by
  induction h with
  | nil =>
      intro σ st ρG ρC hc hr _
      exact ⟨_, Exec.skip, st, ρC, rfl, hc, hr⟩
  | @cons Γ Λ Λ' Λ'' K s rest cs cr hs _ ih =>
      intro σ st ρG ρC hc hr hnf
      have hex : execBlock X.O X.passes X.R (Block.cons s rest) σ ρG =
          match execStmt X.O X.passes X.R s σ ρG with
          | .ok σ' ρ' => execBlock X.O X.passes X.R rest σ' ρ'
          | o => o := rfl
      rw [hex] at hnf ⊢
      cases hs' : execStmt X.O X.passes X.R s σ ρG with
      | ok σ' ρ' =>
          rw [hs'] at hnf
          obtain ⟨o1, h1, hO⟩ := hs σ st ρG ρC hc hr (by rw [hs']; rfl)
          rw [hs'] at hO
          obtain ⟨st1, ρC1, ho1, hc1, hr1⟩ := hO
          subst ho1
          obtain ⟨o2, h2, hO2⟩ := ih σ' st1 ρ' ρC1 hc1 hr1 hnf
          exact ⟨o2, Exec.seqN h1 h2, hO2⟩
      | zurueck σ' v =>
          obtain ⟨o1, h1, hO⟩ := hs σ st ρG ρC hc hr (by rw [hs']; rfl)
          rw [hs'] at hO
          obtain ⟨st1, cv, ho1, hc1, hrc⟩ := hO
          subst ho1
          exact ⟨_, Exec.seqX h1 rfl, st1, cv, rfl, hc1, hrc⟩
      | grund σ' r =>
          obtain ⟨o1, -, hO⟩ := hs σ st ρG ρC hc hr (by rw [hs']; rfl)
          rw [hs'] at hO
          exact hO.elim
      | leave hl σ' ρ' =>
          obtain ⟨o1, h1, hO⟩ := hs σ st ρG ρC hc hr (by rw [hs']; rfl)
          rw [hs'] at hO
          obtain ⟨st1, ρC1, ho1, hc1, hr1⟩ := hO
          subst ho1
          exact ⟨_, Exec.seqX h1 rfl, st1, ρC1, rfl, hc1, hr1⟩
      | next hl σ' ρ' =>
          obtain ⟨o1, h1, hO⟩ := hs σ st ρG ρC hc hr (by rw [hs']; rfl)
          rw [hs'] at hO
          obtain ⟨st1, ρC1, ho1, hc1, hr1⟩ := hO
          subst ho1
          exact ⟨_, Exec.seqX h1 rfl, st1, ρC1, rfl, hc1, hr1⟩
      | logik e => rw [hs'] at hnf; exact Bool.noConfusion hnf
      | hardware e => rw [hs'] at hnf; exact Bool.noConfusion hnf
  | @bind Γ Λ Λ' K τ e rest x τc ce cr hK hf he hd _ ih =>
      intro σ st ρG ρC hc hr hnf
      have hex : execBlock X.O X.passes X.R (Block.bind e rest) σ ρG =
          (execBlock X.O X.passes X.R rest (σ.lese Λ e.orte)
            (.cons (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρG) ρG)).schrumpf := rfl
      rw [hex] at hnf ⊢
      rw [istFehler_schrumpf] at hnf
      have hc' : corrW X.EL (σ.lese Λ e.orte) st := (corrW_lese _ _ _ _ _).mpr hc
      obtain ⟨v, st1, h1, hv, hc1⟩ := he.run X K hc' hr
      have hr1 := envRel_push hK hf hr _ v hv
      obtain ⟨o, h2, hO⟩ := ih _ st1 _ (lokUpd ρC x v) hc1 hr1 hnf
      exact ⟨o, Exec.seqN (Exec.set h1 (convV_of_valCorr hv hd)) h2, stOut_schrumpf X m _ o hO⟩
  | pre he _ ih =>
      intro σ st ρG ρC hc hr hnf
      obtain ⟨st1, h1, hc1⟩ := pre_run he hc hr
      obtain ⟨o, h2, hO⟩ := ih σ st1 ρG ρC hc1 hr hnf
      exact ⟨o, Exec.seqN h1 h2, hO⟩

/-! ### Terminal blocks (`Endblock`): the function body -/

/-- The outcome relation of a terminal block. At the TOP of a `void`
    function, falling off the end is `return;` (`top`): the emitter writes
    no final `return;` there (`beispiele/104`, `einzahlen`). -/
def EndOut (X : TVCtx D) (m : Nat) (top : Bool) {Γ : Ctx} (K : CEnvLay D Γ) {V : Vertrag D}
    {l : Bool} : EndAusgang V l Γ → COut → Prop
  | .zurueck σ' v, o => ∃ st', corrW X.EL σ' st' ∧
      ((∃ cv, o = .ret st' cv ∧ RetCorr X.EL V.erg v cv) ∨
        (top = true ∧ V.erg = none ∧ ∃ ρC', o = .norm st' ρC'))
  | .grund _ _, _ => False
  | .leave _ σ' ρG', o =>
      ∃ st' ρC', o = .jump (.ende m) st' ρC' ∧ corrW X.EL σ' st' ∧ EnvRel X.EL K ρG' ρC'
  | .next _ σ' ρG', o =>
      ∃ st' ρC', o = .jump (.weiter m) st' ρC' ∧ corrW X.EL σ' st' ∧ EnvRel X.EL K ρG' ρC'
  | .logik _, _ => False
  | .hardware _, _ => False

def EndAusgang.istFehler {V : Vertrag D} {l : Bool} {Γ : Ctx} : EndAusgang V l Γ → Bool
  | .logik _ => true
  | .hardware _ => true
  | _ => false

/-- The judgement for `execEnd`. -/
def EndSem (X : TVCtx D) (m : Nat) (top : Bool) {Γ : Ctx} (K : CEnvLay D Γ) {V : Vertrag D}
    {l : Bool} {Λ : List (Res D)} (b : Endblock D V l Γ Λ) (cs : CS) : Prop :=
  ∀ (σ : World D) (st : CSt) (ρG : Env D Γ) (ρC : CLok), corrW X.EL σ st →
    EnvRel X.EL K ρG ρC → (execEnd X.O X.passes X.R b σ ρG).istFehler = false →
    ∃ o, Exec X.EL.lay X.orc X.fr X.CR X.XR cs st ρC o ∧
      EndOut X m top K (execEnd X.O X.passes X.R b σ ρG) o

/-- The terminal-block correspondence. -/
inductive EndCorr (X : TVCtx D) (m : Nat) (top : Bool) {V : Vertrag D} {l : Bool} :
    {Γ : Ctx} → {Λ : List (Res D)} → CEnvLay D Γ → Endblock D V l Γ Λ → CS → Prop where
  | ret {Γ : Ctx} {Λ : List (Res D)} {K : CEnvLay D Γ} {r : ErgExpr D Γ Λ V.erg}
      {cr : Option (CTy × CX)} (hΛ : Λ.Perm V.ende) (h : ErgCorr X K r cr) :
      EndCorr X m top K (.ret r hΛ) (.ret cr)
  | retEnd {Γ : Ctx} {Λ : List (Res D)} {K : CEnvLay D Γ} {r : ErgExpr D Γ Λ V.erg}
      (hΛ : Λ.Perm V.ende) (htop : top = true) (hV : V.erg = none) :
      EndCorr X m top K (.ret r hΛ) .skip
  | leave {Γ : Ctx} {Λ : List (Res D)} {K : CEnvLay D Γ} (hl : l = true) :
      EndCorr X m top K (Endblock.leave (Λ := Λ) hl) (.goto (.ende m))
  | next {Γ : Ctx} {Λ : List (Res D)} {K : CEnvLay D Γ} (hl : l = true) :
      EndCorr X m top K (Endblock.next (Λ := Λ) hl) (.goto (.weiter m))
  | cons {Γ : Ctx} {Λ Λ' : List (Res D)} {K : CEnvLay D Γ} {s : Stmt D V l Γ Λ Λ'}
      {rest : Endblock D V l Γ Λ'} {cs cr : CS} (hs : StmtCorr X m K s cs)
      (hr : EndCorr X m top K rest cr) : EndCorr X m top K (.cons s rest) (.seq cs cr)
  | bind {Γ : Ctx} {Λ : List (Res D)} {K : CEnvLay D Γ} {τ : Ty} {e : Expr D Γ Λ τ}
      {rest : Endblock D V l (τ :: Γ) Λ} {x : Nat} {τc : CTy} {ce : CX} {cr : CS}
      (hK : K.okB = true) (hf : K.freshB x = true) (he : ExprCorr X K ce e)
      (hd : declOk τ τc = true) (hr : EndCorr X m top (K.push τ x) rest cr) :
      EndCorr X m top K (.bind e rest) (.seq (.set x τc ce) cr)
  | pre {Γ : Ctx} {Λ Λ0 : List (Res D)} {K : CEnvLay D Γ} {b : Endblock D V l Γ Λ}
      {τ0 : Ty} {e0 : Expr D Γ Λ0 τ0} {ce : CX} {cr : CS} (he : ExprCorr X K ce e0)
      (hr : EndCorr X m top K b cr) : EndCorr X m top K b (.seq (.expr ce) cr)

theorem endIstFehler_schrumpf {V : Vertrag D} {l : Bool} {Γ : Ctx} {τ : Ty}
    (a : EndAusgang V l (τ :: Γ)) : a.schrumpf.istFehler = a.istFehler := by
  cases a <;> rfl

theorem endOut_schrumpf (X : TVCtx D) (m : Nat) (top : Bool) {Γ : Ctx} {K : CEnvLay D Γ}
    {τ : Ty} {x : Nat} {V : Vertrag D} {l : Bool} (a : EndAusgang V l (τ :: Γ)) (o : COut)
    (h : EndOut X m top (K.push τ x) a o) : EndOut X m top K a.schrumpf o := by
  cases a with
  | zurueck σ v => exact h
  | grund σ r => exact h.elim
  | leave hl σ ρ =>
      obtain ⟨st', ρC', ho, hc, hr⟩ := h
      exact ⟨st', ρC', ho, hc, envRel_pop hr⟩
  | next hl σ ρ =>
      obtain ⟨st', ρC', ho, hc, hr⟩ := h
      exact ⟨st', ρC', ho, hc, envRel_pop hr⟩
  | logik e => exact h.elim
  | hardware e => exact h.elim

/-- THE TERMINAL-BLOCK THEOREM (a function body is an `Endblock`). -/
theorem cCorr_end (X : TVCtx D) (m : Nat) (top : Bool) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} {K : CEnvLay D Γ} {b : Endblock D V l Γ Λ} {cb : CS}
    (h : EndCorr X m top K b cb) : EndSem X m top K b cb := by
  induction h with
  | @ret Γ Λ K r cr hΛ hrc =>
      intro σ st ρG ρC hc hr _
      have hc' : corrW X.EL (σ.lese Λ r.orte) st := (corrW_lese _ _ _ _ _).mpr hc
      obtain ⟨st', cv, he, hc1, hret⟩ := ergCorr_run X K hrc hc' hr
      exact ⟨_, he, st', hc1, Or.inl ⟨cv, rfl, hret⟩⟩
  | @retEnd Γ Λ K r hΛ htop hV =>
      intro σ st ρG ρC hc hr _
      exact ⟨_, Exec.skip, st, (corrW_lese _ _ _ _ _).mpr hc, Or.inr ⟨htop, hV, ρC, rfl⟩⟩
  | leave hl =>
      intro σ st ρG ρC hc hr _
      exact ⟨_, Exec.goto, st, ρC, rfl, hc, hr⟩
  | next hl =>
      intro σ st ρG ρC hc hr _
      exact ⟨_, Exec.goto, st, ρC, rfl, hc, hr⟩
  | @cons Γ Λ Λ' K s rest cs cr hs _ ih =>
      intro σ st ρG ρC hc hr hnf
      have hex : execEnd X.O X.passes X.R (Endblock.cons s rest) σ ρG =
          match execStmt X.O X.passes X.R s σ ρG with
          | .ok σ' ρ' => execEnd X.O X.passes X.R rest σ' ρ'
          | .zurueck σ' v => .zurueck σ' v
          | .grund σ' r => .grund σ' r
          | .leave h σ' ρ' => .leave h σ' ρ'
          | .next h σ' ρ' => .next h σ' ρ'
          | .logik e => .logik e
          | .hardware e => .hardware e := rfl
      rw [hex] at hnf ⊢
      cases hs' : execStmt X.O X.passes X.R s σ ρG with
      | ok σ' ρ' =>
          rw [hs'] at hnf
          obtain ⟨o1, h1, hO⟩ := hs σ st ρG ρC hc hr (by rw [hs']; rfl)
          rw [hs'] at hO
          obtain ⟨st1, ρC1, ho1, hc1, hr1⟩ := hO
          subst ho1
          obtain ⟨o2, h2, hO2⟩ := ih σ' st1 ρ' ρC1 hc1 hr1 hnf
          exact ⟨o2, Exec.seqN h1 h2, hO2⟩
      | zurueck σ' v =>
          obtain ⟨o1, h1, hO⟩ := hs σ st ρG ρC hc hr (by rw [hs']; rfl)
          rw [hs'] at hO
          obtain ⟨st1, cv, ho1, hc1, hrc⟩ := hO
          subst ho1
          exact ⟨_, Exec.seqX h1 rfl, st1, hc1, Or.inl ⟨cv, rfl, hrc⟩⟩
      | grund σ' r =>
          obtain ⟨o1, -, hO⟩ := hs σ st ρG ρC hc hr (by rw [hs']; rfl)
          rw [hs'] at hO
          exact hO.elim
      | leave hl σ' ρ' =>
          obtain ⟨o1, h1, hO⟩ := hs σ st ρG ρC hc hr (by rw [hs']; rfl)
          rw [hs'] at hO
          obtain ⟨st1, ρC1, ho1, hc1, hr1⟩ := hO
          subst ho1
          exact ⟨_, Exec.seqX h1 rfl, st1, ρC1, rfl, hc1, hr1⟩
      | next hl σ' ρ' =>
          obtain ⟨o1, h1, hO⟩ := hs σ st ρG ρC hc hr (by rw [hs']; rfl)
          rw [hs'] at hO
          obtain ⟨st1, ρC1, ho1, hc1, hr1⟩ := hO
          subst ho1
          exact ⟨_, Exec.seqX h1 rfl, st1, ρC1, rfl, hc1, hr1⟩
      | logik e => rw [hs'] at hnf; exact Bool.noConfusion hnf
      | hardware e => rw [hs'] at hnf; exact Bool.noConfusion hnf
  | @bind Γ Λ K τ e rest x τc ce cr hK hf he hd _ ih =>
      intro σ st ρG ρC hc hr hnf
      have hex : execEnd X.O X.passes X.R (Endblock.bind e rest) σ ρG =
          (execEnd X.O X.passes X.R rest (σ.lese Λ e.orte)
            (.cons (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρG) ρG)).schrumpf := rfl
      rw [hex] at hnf ⊢
      rw [endIstFehler_schrumpf] at hnf
      have hc' : corrW X.EL (σ.lese Λ e.orte) st := (corrW_lese _ _ _ _ _).mpr hc
      obtain ⟨v, st1, h1, hv, hc1⟩ := he.run X K hc' hr
      have hr1 := envRel_push hK hf hr _ v hv
      obtain ⟨o, h2, hO⟩ := ih _ st1 _ (lokUpd ρC x v) hc1 hr1 hnf
      exact ⟨o, Exec.seqN (Exec.set h1 (convV_of_valCorr hv hd)) h2,
        endOut_schrumpf X m top _ o hO⟩
  | pre he _ ih =>
      intro σ st ρG ρC hc hr hnf
      obtain ⟨st1, h1, hc1⟩ := pre_run he hc hr
      obtain ⟨o, h2, hO⟩ := ih σ st1 ρG ρC hc1 hr hnf
      exact ⟨o, Exec.seqN h1 h2, hO⟩

end Gabbro.Grammatik
