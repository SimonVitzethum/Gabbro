/-
  File:      Grammatik/CFormenM.lean
  Subject:   T4 pass (ii): the medium forms and their correspondence.

  THE FORMS OF THIS PASS (emit.rs shapes; the survey of 2026-09-13)
    M1  `k->slots[i].f` through `T *restrict k`, and through a Gabbro
        pointer (`p->f`)                      slot / durch      ecorr_slotParam, ecorr_durch
    M2  `k->slots[i].f = e;` and `p->f = e;`  assignSlot / assignDurch
                                                                scorr_assignSlotParam, scorr_assignDurch
    M3  `a && b`, `a || b` (short-circuit)    und / oder        ecorr_und, ecorr_oder
    M4  `c ? a : b`                           (no constructor)  ev_condT/F, cond_max
    M5  `(uint32_t)(sizeof(k->slots) / sizeof(k->slots[0]))`
                                              the slot count    ev_sizeofQuot, hiSlots_ev
    M6  `static const uintN_t c[N] = {…};` and `c[i]`
                                              (no constructor)  constTab_read, ro_store_stuck
    M7  `f(k, i);`, `T x = f(k, i);` with pointer, scalar and fixed
        parameters                            call / bindCall   scorr_call, bsem_bindCall
        the call itself                       rufAt             cCorr_ruf
    M8  `L_nimm(); { … } L_gib();`, a release before `return`
                                              locks             scorr_locks, scorr_extPre
    M9  `{ uint32_t _o = e; if (_o != T_NONE) { uint32_t x = _o; … } else { … } }`
                                              onOption          scorr_onOption
    M10 `T x = (T){ .f = v, … };` and `x.f` (a by-value struct local,
        a stack block of the frame)           (no constructor)  structLocal_rw
    M11 the `_Static_assert` prelude          (compile-time)    prelude_pins, sizeof_pos
    M12 explicit integer casts: pass (i) `ecorr_cast`; widening `u64(a)`
        is `ecorr_cast` over `weiter`
-/
import Grammatik.CFormenI

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- Evaluation rule of a load. -/
theorem ev_ld {L : CLayout} {orc : DevOrc} {fr : Nat} {p : CX} {τ : CTy} {st st1 : CSt}
    {ρ : CLok} {q : CPtr} {v : CVal} (hp : ev L orc fr p st ρ = some (.ptr q, st1))
    (hl : bLoad L st1 q τ = some v) : ev L orc fr (.ld p τ) st ρ = some (v, st1) := by
  simp only [ev, hp, hl]

/-! ## 1. M1/M2: places through a pointer -/

section Zeiger

variable (X : TVCtx D) {Γ : Ctx} {Λ : List (Res D)} (K : CEnvLay D Γ)

/-- A C expression that denotes the address of table `t`'s object: the
    named storage `T_speicher`, a pointer parameter `T *restrict k`, or the
    C local of a Gabbro pointer variable. It evaluates without effect. -/
def PtrTo (cp : CX) (t : D.Tab) : Prop :=
  ∀ (st : CSt) (ρG : Env D Γ) (ρC : CLok), EnvRel X.EL K ρG ρC →
    ev X.EL.lay X.orc X.fr cp st ρC = some (.ptr ⟨.tab (X.EL.tnr t), 0⟩, st)

theorem ptrTo_named (t : D.Tab) : PtrTo X K (.addr (.tab (X.EL.tnr t))) t :=
  fun _ _ _ _ => rfl

/-- `T *restrict k`: the parameter the certificate says points to `t`. -/
theorem ptrTo_param {k : Nat} {t : D.Tab} (hk : (k, t) ∈ K.pp) : PtrTo X K (.var k) t := by
  intro st ρG ρC hr
  have h := hr.2.1 _ hk
  simp only [ev, h]

/-- The C local of a Gabbro pointer variable of table number `n`. -/
theorem ptrTo_var {n : Nat} {rw : Bool} {t : D.Tab} (x : Var Γ (.ptr n rw))
    (ht : D.tabNr n = some t) : PtrTo X K (.var (K.loc x)) t := by
  intro st ρG ρC hr
  obtain ⟨t', ht', hv⟩ := hr.1 _ x
  rw [ht] at ht'
  cases ht'
  simp only [ev, hv]

/-- The address `p->slots[k].f` for `p` a pointer to `t`. -/
theorem ev_slotVia {cp ci : CX} {t : D.Tab} (hp : PtrTo X K cp t) (f : D.Feld t) {st st1 : CSt}
    {ρG : Env D Γ} {ρC : CLok} (hr : EnvRel X.EL K ρG ρC) {k : Int}
    (hi : ev X.EL.lay X.orc X.fr ci st ρC = some (.int k, st1)) (k0 : 0 ≤ k)
    (k1 : k < D.count t) :
    ev X.EL.lay X.orc X.fr (.slotA cp ci (X.EL.trec t).count (X.EL.trec t).ssize
      ((X.EL.trec t).off (X.EL.fnr t f))) st ρC = some (.ptr (X.EL.slotPtr t k f), st1) := by
  have hcnt := X.EL.trec_count t
  have hb : 0 ≤ k ∧ k < ((X.EL.trec t).count : Int) := ⟨k0, by omega⟩
  simp only [ev, hp st ρG ρC hr, hi, if_pos hb, ptrAdd_slot X.EL t f k k0 k1]

/-- The load scheme through a pointer. -/
theorem ecorr_slotVia {cp ci : CX} {t : D.Tab} (hp : PtrTo X K cp t) (f : D.Feld t)
    (hgt : D.geist t = false) {i : Expr D Γ Λ (.index (D.count t))} (hi : ExprCorr X K ci i)
    {e : Expr D Γ Λ (D.typ t f)}
    (hev : ∀ (σ : World D) (ρG : Env D Γ), eval σ e σ ρG = σ.slots t (eval σ i σ ρG).n f) :
    ExprCorr X K (.ld (.slotA cp ci (X.EL.trec t).count (X.EL.trec t).ssize
      ((X.EL.trec t).off (X.EL.fnr t f))) (X.EL.slotTy t f)) e := by
  intro σ st ρG ρC hc hr
  obtain ⟨st1, h1, hc1⟩ := hi.runI X K hc hr
  have k0 := (eval σ i σ ρG).lo_le
  have k1 := (eval σ i σ ρG).le_hi
  have ha := ev_slotVia X K hp f hr h1 k0 (by omega)
  have hl := corr_leseSlot X.EL σ st1 hc1 t hgt (eval σ i σ ρG).n f k0 (by omega)
  refine ⟨.int (encW (D.typ t f) (σ.slots t (eval σ i σ ρG).n f)), st1, ev_ld ha hl, ?_⟩
  rw [hev]; exact valCorr_encW _ _ _ (X.EL.fnr_fits t f)

/-- M1. `k->slots[i].f` with `k` the pointer parameter to `t` (the
    `beispiele/104` shape: `return k->slots[i].stand;`). -/
theorem ecorr_slotParam {k : Nat} {t : D.Tab} (hk : (k, t) ∈ K.pp) (f : D.Feld t)
    (hgt : D.geist t = false) {ci : CX} {i : Expr D Γ Λ (.index (D.count t))} (hL : darf D t Λ)
    (hi : ExprCorr X K ci i) :
    ExprCorr X K (.ld (.slotA (.var k) ci (X.EL.trec t).count (X.EL.trec t).ssize
      ((X.EL.trec t).off (X.EL.fnr t f))) (X.EL.slotTy t f)) (Expr.slot t f i hL) :=
  ecorr_slotVia X K (ptrTo_param X K hk) f hgt hi (fun _ _ => rfl)

/-- M1. `p->f` through a Gabbro pointer expression `p` whose C form points
    to `t` (`durch`). -/
theorem ecorr_durch {n : Nat} {rw : Bool} {p : Expr D Γ Λ (.ptr n rw)} {cp : CX} {t : D.Tab}
    (ht : D.tabNr n = some t) (hp : PtrTo X K cp t) (f : D.Feld t) (hgt : D.geist t = false)
    {ci : CX} {i : Expr D Γ Λ (.index (D.count t))} (hL : darf D t Λ) (hi : ExprCorr X K ci i) :
    ExprCorr X K (.ld (.slotA cp ci (X.EL.trec t).count (X.EL.trec t).ssize
      ((X.EL.trec t).off (X.EL.fnr t f))) (X.EL.slotTy t f)) (Expr.durch p t ht f i hL) :=
  ecorr_slotVia X K hp f hgt hi (fun _ _ => rfl)

/-- The store scheme through a pointer: the emitted store reaches a state
    related to Gabbro's `schreibSlot`. -/
theorem slotStore_exec {cp ci ce : CX} {t : D.Tab} (hp : PtrTo X K cp t) (f : D.Feld t)
    (hgt : D.geist t = false) {i : Expr D Γ Λ (.index (D.count t))} {e : Expr D Γ Λ (D.typ t f)}
    (hi : ExprCorr X K ci i) (he : ExprCorr X K ce e) (Λw : List (Res D)) {σ : World D}
    {st : CSt} {ρG : Env D Γ} {ρC : CLok} (hc : corrW X.EL σ st) (hr : EnvRel X.EL K ρG ρC) :
    ∃ st', Exec X.EL.lay X.orc X.fr X.CR X.XR
        (.store (.slotA cp ci (X.EL.trec t).count (X.EL.trec t).ssize
          ((X.EL.trec t).off (X.EL.fnr t f))) (X.EL.slotTy t f) ce) st ρC (.norm st' ρC) ∧
      corrW X.EL (σ.schreibSlot t Λw (eval σ i σ ρG).n f (eval σ e σ ρG)) st' := by
  obtain ⟨st1, h1, hc1⟩ := hi.runI X K hc hr
  obtain ⟨v, st2, h2, hv, hc2⟩ := he.run X K hc1 hr
  have k0 := (eval σ i σ ρG).lo_le
  have k1 := (eval σ i σ ρG).le_hi
  have ha := ev_slotVia X K hp f hr h1 k0 (by omega)
  have hve := valCorr_int_of_fits _ _ _ _ (X.EL.fnr_fits t f) hv
  subst hve
  obtain ⟨st3, hs, hc3, -⟩ := corr_schreibSlot X.EL σ st2 hc2 t hgt Λw (eval σ i σ ρG).n f
    (eval σ e σ ρG) k0 (by omega)
  exact ⟨st3, Exec.store ha h2 (convV_of_valFits _ _ (encW_fits _ _ _ (X.EL.fnr_fits t f))) hs,
    hc3⟩

/-- M2. `k->slots[i].f = e;` through the pointer parameter (the
    `beispiele/104` shape: `k->slots[i].stand = 100;`), against the Gabbro
    store to the table. -/
theorem scorr_assignSlotParam (m : Nat) {V : Vertrag D} {l : Bool} {k : Nat} {t : D.Tab}
    (hk : (k, t) ∈ K.pp) (f : D.Feld t) (hgt : D.geist t = false)
    {i : Expr D Γ Λ (.index (D.count t))} {e : Expr D Γ Λ (D.typ t f)} {ci ce : CX}
    (hw : V.schreibt t = true) (hL : darf D t Λ) (hi : ExprCorr X K ci i)
    (he : ExprCorr X K ce e) :
    StmtCorr X m K (Stmt.assignSlot (l := l) t f i e hw hL)
      (.store (.slotA (.var k) ci (X.EL.trec t).count (X.EL.trec t).ssize
        ((X.EL.trec t).off (X.EL.fnr t f))) (X.EL.slotTy t f) ce) := by
  intro σ st ρG ρC hc hr _
  obtain ⟨st', hx, hc'⟩ := slotStore_exec X K (ptrTo_param X K hk) f hgt hi he Λ
    ((corrW_lese _ _ _ _ _).mpr hc : corrW X.EL (σ.lese Λ (i.orte ++ e.orte)) st) hr
  exact ⟨_, hx, st', ρC, rfl, hc', hr⟩

/-- M2. `p->f = e;` through a `rw` pointer (`assignDurch`). -/
theorem scorr_assignDurch (m : Nat) {V : Vertrag D} {l : Bool} {n : Nat}
    {p : Expr D Γ Λ (.ptr n true)} {cp : CX} {t : D.Tab} (ht : D.tabNr n = some t)
    (hp : PtrTo X K cp t) (f : D.Feld t) (hgt : D.geist t = false)
    {i : Expr D Γ Λ (.index (D.count t))} {e : Expr D Γ Λ (D.typ t f)} {ci ce : CX}
    (hw : V.schreibt t = true) (hL : darf D t Λ) (hi : ExprCorr X K ci i)
    (he : ExprCorr X K ce e) :
    StmtCorr X m K (Stmt.assignDurch (l := l) p t ht f i e hw hL)
      (.store (.slotA cp ci (X.EL.trec t).count (X.EL.trec t).ssize
        ((X.EL.trec t).off (X.EL.fnr t f))) (X.EL.slotTy t f) ce) := by
  intro σ st ρG ρC hc hr _
  obtain ⟨st', hx, hc'⟩ := slotStore_exec X K hp f hgt hi he Λ
    ((corrW_lese _ _ _ _ _).mpr hc : corrW X.EL (σ.lese Λ (p.orte ++ i.orte ++ e.orte)) st) hr
  exact ⟨_, hx, st', ρC, rfl, hc', hr⟩

/-! ## 2. M3: `&&` and `||`, short-circuit -/

/-- M3. `a && b`: the right operand is evaluated only when the left is
    true (6.5.13p4); Gabbro's `und` evaluates both, and both are pure, so
    the values agree (the C side makes fewer observations). -/
theorem ecorr_und {ca cb : CX} {a b : Expr D Γ Λ .bool} (ha : ExprCorr X K ca a)
    (hb : ExprCorr X K cb b) : ExprCorr X K (.land ca cb) (.und a b) := by
  intro σ st ρG ρC hc hr
  obtain ⟨st1, h1, hc1⟩ := ha.runB X K hc hr
  cases hav : wahr? (eval σ a σ ρG) with
  | false =>
      rw [hav] at h1
      refine ⟨.int 0, st1, ?_, ?_⟩
      · simp only [ev, h1, truth_b2i]
      · show CVal.int 0 = .int (if (wahr? (eval σ a σ ρG) && wahr? (eval σ b σ ρG)) then 1 else 0)
        rw [hav]; rfl
  | true =>
      rw [hav] at h1
      obtain ⟨st2, h2, -⟩ := hb.runB X K hc1 hr
      refine ⟨.int (b2i (wahr? (eval σ b σ ρG))), st2, ?_, ?_⟩
      · simp only [ev, h1, truth_b2i, h2]
      · show CVal.int (b2i (wahr? (eval σ b σ ρG))) =
          .int (if (wahr? (eval σ a σ ρG) && wahr? (eval σ b σ ρG)) then 1 else 0)
        rw [hav]; rfl

/-- M3. `a || b`. -/
theorem ecorr_oder {ca cb : CX} {a b : Expr D Γ Λ .bool} (ha : ExprCorr X K ca a)
    (hb : ExprCorr X K cb b) : ExprCorr X K (.lor ca cb) (.oder a b) := by
  intro σ st ρG ρC hc hr
  obtain ⟨st1, h1, hc1⟩ := ha.runB X K hc hr
  cases hav : wahr? (eval σ a σ ρG) with
  | true =>
      rw [hav] at h1
      refine ⟨.int 1, st1, ?_, ?_⟩
      · simp only [ev, h1, truth_b2i]
      · show CVal.int 1 = .int (if (wahr? (eval σ a σ ρG) || wahr? (eval σ b σ ρG)) then 1 else 0)
        rw [hav]; rfl
  | false =>
      rw [hav] at h1
      obtain ⟨st2, h2, -⟩ := hb.runB X K hc1 hr
      refine ⟨.int (b2i (wahr? (eval σ b σ ρG))), st2, ?_, ?_⟩
      · simp only [ev, h1, truth_b2i, h2]
      · show CVal.int (b2i (wahr? (eval σ b σ ρG))) =
          .int (if (wahr? (eval σ a σ ρG) || wahr? (eval σ b σ ρG)) then 1 else 0)
        rw [hav]; rfl

end Zeiger

/-! ## 3. M4: the conditional expression -/

/-- M4. `c ? a : b` with a true condition evaluates only `a`. -/
theorem ev_condT {L : CLayout} {orc : DevOrc} {fr : Nat} {t : CIT} {c a b : CX} {st st1 st2 : CSt}
    {ρ : CLok} {v : CVal} {x y : Int} (hc : ev L orc fr c st ρ = some (v, st1))
    (ht : truth v = some true) (ha : ev L orc fr a st1 ρ = some (.int x, st2))
    (hx : conv t x = some y) : ev L orc fr (.cond t c a b) st ρ = some (.int y, st2) := by
  simp only [ev, hc, ht, ha, hx]

/-- M4. … and with a false one only `b`. -/
theorem ev_condF {L : CLayout} {orc : DevOrc} {fr : Nat} {t : CIT} {c a b : CX} {st st1 st2 : CSt}
    {ρ : CLok} {v : CVal} {x y : Int} (hc : ev L orc fr c st ρ = some (v, st1))
    (ht : truth v = some false) (hb : ev L orc fr b st1 ρ = some (.int x, st2))
    (hx : conv t x = some y) : ev L orc fr (.cond t c a b) st ρ = some (.int y, st2) := by
  simp only [ev, hc, ht, hb, hx]

/-- M4. The emitted merge `(z > v) ? z : v` (2339) computes the maximum,
    for `z` and `v` in `t`. -/
theorem cond_max {L : CLayout} {orc : DevOrc} {fr : Nat} (t : CIT) (st : CSt) (ρ : CLok)
    (z v : Nat) (x y : Int) (hz : ρ z = .int x) (hv : ρ v = .int y)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hy : t.lo ≤ y ∧ y ≤ t.hi) :
    ev L orc fr (.cond t (.cmp .gt t (.var z) (.var v)) (.var z) (.var v)) st ρ =
      some (.int (max x y), st) := by
  have hcx := conv_id hx
  have hcy := conv_id hy
  have hcmp : ev L orc fr (.cmp .gt t (.var z) (.var v)) st ρ =
      some (.int (b2i (decide (y < x))), st) := ev_cmp (ev_var hz) (ev_var hv) hcx hcy
  by_cases h : y < x
  · rw [show max x y = x by omega]
    exact ev_condT hcmp (by rw [decide_eq_true h]; rfl) (ev_var hz) hcx
  · rw [show max x y = y by omega]
    exact ev_condF hcmp (by rw [decide_eq_false h]; rfl) (ev_var hv) hcy

/-! ## 4. M5: `sizeof` in the loop header -/

/-- `(T)(sizeof(a) / sizeof(a[0]))`: two `size_t` (`uint64_t`) constants
    the layout computes, divided, converted. -/
def sizeofQuot (t : CIT) (sz es : Nat) : CX := .cast t (.bin .div CIT.u64 (.szof sz) (.szof es))

/-- M5. The quotient is the element count, without effect. -/
theorem ev_sizeofQuot (L : CLayout) (orc : DevOrc) (fr : Nat) (t : CIT) (n es : Nat)
    (hes : 0 < es) (hsz : ((n * es : Nat) : Int) ≤ 2 ^ 64 - 1) (hes' : (es : Int) ≤ 2 ^ 64 - 1)
    (hn : (n : Int) ≤ t.hi) (st : CSt) (ρ : CLok) :
    ev L orc fr (sizeofQuot t (n * es) es) st ρ = some (.int n, st) := by
  have u64hi : CIT.u64.hi = 2 ^ 64 - 1 := by decide
  have c1 : conv CIT.u64 ((n * es : Nat) : Int) = some ((n * es : Nat) : Int) :=
    conv_id ⟨by show (0 : Int) ≤ _; omega, by omega⟩
  have c2 : conv CIT.u64 (es : Int) = some (es : Int) :=
    conv_id ⟨by show (0 : Int) ≤ _; omega, by omega⟩
  have hdiv : cArith .div CIT.u64 ((n * es : Nat) : Int) (es : Int) = some (n : Int) := by
    show (if (es : Int) = 0 ∨ (CIT.u64.sgn = true ∧ _ = CIT.u64.lo ∧ (es : Int) = -1) then none
      else some (((n * es : Nat) : Int).tdiv (es : Int))) = _
    rw [if_neg (by
      intro h
      rcases h with h | ⟨h, -⟩
      · omega
      · exact absurd h (by decide))]
    congr 1
    rw [Int.tdiv_eq_ediv_nonneg (by omega), Int.natCast_mul, Int.mul_ediv_cancel _ (by omega)]
  have c3 : conv t (n : Int) = some (n : Int) :=
    conv_id ⟨by have := CIT.lo_le_zero t; omega, hn⟩
  exact ev_cast t (ev_bin rfl rfl c1 c2 hdiv) c3

/-- The `traverse` header's bound for table `t`: `sizeof(k->slots)` is the
    object's size, `sizeof(k->slots[0])` the record's. -/
def hiSlots (EL : EmitLay D) (t : D.Tab) : CX :=
  sizeofQuot CIT.u32 (EL.trec t).size (EL.trec t).ssize

/-- M5. It evaluates to the slot count, in every state: this discharges
    `scorr_traverse`'s bound premise. -/
theorem hiSlots_ev (X : TVCtx D) (t : D.Tab) (hes : 0 < (X.EL.trec t).ssize)
    (hsz : (((X.EL.trec t).size : Nat) : Int) ≤ 2 ^ 64 - 1)
    (hes' : (((X.EL.trec t).ssize : Nat) : Int) ≤ 2 ^ 64 - 1) (hn : D.count t ≤ CIT.u32.hi)
    (st : CSt) (ρ : CLok) :
    ev X.EL.lay X.orc X.fr (hiSlots X.EL t) st ρ = some (.int (D.count t), st) := by
  have hc := X.EL.trec_count t
  have e := ev_sizeofQuot X.EL.lay X.orc X.fr CIT.u32 (X.EL.trec t).count (X.EL.trec t).ssize hes
    hsz hes' (by omega) st ρ
  rw [hc] at e
  exact e

/-! ## 5. M6: `static const` tables -/

/-- The layout of `static const uintN_t c[N]`: `N` cells of one type. -/
def arrLay (τ : CTy) (n : Nat) : RecLay :=
  { count := n, nf := 1, fty := fun _ => τ, off := fun _ => 0, ssize := τ.size }

theorem arrLay_wf (τ : CTy) (n : Nat) : (arrLay τ n).wf = true := by
  simp [RecLay.wf, RecLay.fitsB, RecLay.disjB, arrLay, List.range_succ, Nat.mod_self]

/-- A store to read-only storage is stuck: `static const` data never
    changes (C11 6.7.3p6). -/
theorem ro_store_stuck (L : CLayout) (st : CSt) (c : Nat) (B : BlkLay) (hB : L (.ro c) = some B)
    (hk : B.kind = .readonly) (o : Int) (τ : CTy) (v : CVal) :
    bStore L st ⟨.ro c, o⟩ τ v = none := by
  apply storeUB_stuck
  exact .acc (.mode B hB (by rw [hk]; rfl))

/-- M6. `c[i]` reads literal `k` of the table: the `static const` block has
    the array layout, is alive, and holds the literals (its initialiser);
    `i` evaluates to `k < N`. -/
theorem constTab_read (L : CLayout) (orc : DevOrc) (fr : Nat) (c : Nat) (τ : CTy)
    (vals : List Int) (hL : L (.ro c) = some { lay := arrLay τ vals.length, kind := .readonly, base := 0 })
    (st : CSt) (hlive : st.live (.ro c) = true)
    (hmem : ∀ k (hk : k < vals.length), st.mem (.ro c) (k * τ.size) = .int vals[k])
    (ρ : CLok) (ci : CX) (k : Nat) (hk : k < vals.length) (st1 : CSt)
    (hi : ev L orc fr ci st ρ = some (.int k, st1)) (hs : SameML st st1) :
    ev L orc fr (.ld (.idx (.addr (.ro c)) ci vals.length τ.size) τ) st ρ =
      some (.int vals[k], st1) := by
  have hsz := τ.size_pos
  have hkk : k * τ.size + τ.size ≤ vals.length * τ.size := by
    have := Nat.mul_le_mul_right τ.size hk
    rw [Nat.succ_mul] at this
    omega
  have hp : ptrAdd L ⟨.ro c, 0⟩ ((k : Int) * (τ.size : Int)) 1 = some ⟨.ro c, ((k * τ.size : Nat) : Int)⟩ := by
    have e1 : (0 : Int) + (k : Int) * (τ.size : Int) * ((1 : Nat) : Int) = ((k * τ.size : Nat) : Int) := by
      rw [Int.natCast_one, Int.mul_one, Int.zero_add, Int.natCast_mul]
    rw [ptrAdd_progress L ⟨.ro c, 0⟩ _ 1 _ hL (by show (0 : Int) ≤ _; rw [e1]; omega)
      (by show (0 : Int) + _ ≤ (((vals.length * τ.size : Nat)) : Int); rw [e1]; omega)]
    show some (CPtr.mk (.ro c) ((0 : Int) + (k : Int) * (τ.size : Int) * ((1 : Nat) : Int))) = _
    rw [e1]
  have hcell : (arrLay τ vals.length).cell (k * τ.size) = some τ := by
    have := RecLay.cell_pos (arrLay_wf τ vals.length) (j := 0) (by show 0 < 1; omega) (k := k) hk
    simpa [arrLay] using this
  have hacc : accOk L st1 ⟨.ro c, ((k * τ.size : Nat) : Int)⟩ τ .rd = true := by
    unfold accOk
    rw [show (⟨.ro c, ((k * τ.size : Nat) : Int)⟩ : CPtr).blk = .ro c from rfl, hL]
    dsimp only
    rw [show st1.live (.ro c) = true by rw [hs.2]; exact hlive,
      show ((k * τ.size : Nat) : Int).toNat = k * τ.size from Int.toNat_natCast _, hcell]
    simp only [BKind.permits, Bool.true_and, decide_true, Bool.and_true, decide_eq_true_eq]
    exact Int.natCast_nonneg _
  have hm : st1.mem (.ro c) (k * τ.size) = .int vals[k] := by rw [hs.1]; exact hmem k hk
  have hload : bLoad L st1 ⟨.ro c, ((k * τ.size : Nat) : Int)⟩ τ = some (.int vals[k]) := by
    have hne : st1.mem (⟨.ro c, ((k * τ.size : Nat) : Int)⟩ : CPtr).blk
        (⟨.ro c, ((k * τ.size : Nat) : Int)⟩ : CPtr).off.toNat ≠ .undef := by
      show st1.mem (.ro c) ((k * τ.size : Nat) : Int).toNat ≠ _
      rw [Int.toNat_natCast, hm]; simp
    rw [bLoad_progress _ _ _ _ hacc hne]
    show some (st1.mem (.ro c) ((k * τ.size : Nat) : Int).toNat) = _
    rw [Int.toNat_natCast, hm]
  have hb : 0 ≤ (k : Int) ∧ (k : Int) < (vals.length : Int) := ⟨by omega, by omega⟩
  simp only [ev, hi, if_pos hb, hp, hload]

end Gabbro.Grammatik
