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

/-! ## 6. M7: calls

A call is related by the callee's relation `FnCorr`: from related states
and arguments that establish the callee's locals relation after C's
parameter passing, the C call returns (or the Gabbro call fails a logic or
hardware clause) in a related state with a corresponding answer.
`cCorr_ruf` builds it for `rufAt` from the callee body's correspondence;
`scorr_call` and `bsem_bindCall` use it at the call site. -/

def RufAusgang.istFehler {f : D.Fn} : RufAusgang f → Bool
  | .logik _ => true
  | .hardware _ => true
  | _ => false

/-- The outcome relation of a call. -/
def RufOut (EL : EmitLay D) {f : D.Fn} : RufAusgang f → CSt → Option CVal → Prop
  | .ok σ' v, st', rv => corrW EL σ' st' ∧ RetCorr EL (D.erg f) v rv
  | _, _, _ => False

/-- THE CALLEE RELATION: the Gabbro call meaning `R` of `f` against the C
    call meaning `CR` of function `fc` with C parameters `ps`, whose locals
    relation on entry is `Kf`. -/
def FnCorr (EL : EmitLay D) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (CR : CCallR) (f : D.Fn) (fc : Nat) (ps : List (Nat × CTy)) (Kf : CEnvLay D (D.params f)) :
    Prop :=
  ∀ (σ : World D) (st : CSt) (ρG : Env D (D.params f)) (vs : List CVal) (ρ0 : CLok),
    corrW EL σ st → bindParams ps vs = some ρ0 → EnvRel EL Kf ρG ρ0 →
    (R f σ ρG).istFehler = false →
    ∃ st' rv, CR fc st vs st' rv ∧ RufOut EL (R f σ ρG) st' rv

/-- The arguments at a call site: the C arguments evaluate without memory
    effect, and C's parameter passing establishes the callee's locals
    relation for the Gabbro argument values (pointer parameters `k`, fixed
    parameters, scalars). -/
def ArgsTo (X : TVCtx D) {Γ : Ctx} {Λ : List (Res D)} (K : CEnvLay D Γ) {τs : List Ty}
    (args : Args D Γ Λ τs) (cargs : List CX) (ps : List (Nat × CTy)) (Kf : CEnvLay D τs) :
    Prop :=
  ∀ (σ : World D) (st : CSt) (ρG : Env D Γ) (ρC : CLok), corrW X.EL σ st →
    EnvRel X.EL K ρG ρC →
    ∃ vs st' ρ0, evArgs X.EL.lay X.orc X.fr cargs st ρC = some (vs, st') ∧ SameML st st' ∧
      bindParams ps vs = some ρ0 ∧ EnvRel X.EL Kf (evalArgs σ args σ ρG) ρ0

theorem retCorr_ergWert {EL : EmitLay D} {τ : Ty} :
    ∀ {e : Option Ty} (he : e = some τ) (v : ErgVal D e) (rv : Option CVal),
      RetCorr EL e v rv → ∃ c, rv = some c ∧ ValCorr EL τ (ergWert he v) c := by
  intro e he v rv h
  subst he
  exact h

theorem retCorr_none {EL : EmitLay D} : ∀ {e : Option Ty}, e = none → ∀ (v : ErgVal D e),
    RetCorr EL e v none := by
  intro e he v
  subst he
  rfl

section Ruf

variable (X : TVCtx D) {Γ : Ctx} {Λ : List (Res D)} (K : CEnvLay D Γ)

/-- M7. `f(a, b);` -- a call whose answer is dropped (`beispiele/104`:
    `lies(k, i);`). -/
theorem scorr_call (m : Nat) {V : Vertrag D} {l : Bool} (f : D.Fn) (args : Args D Γ Λ (D.params f))
    (hp : RufPasst D V (D.signatur f) Λ) (hr : D.gruende f = 0) {fc : Nat}
    {ps : List (Nat × CTy)} {Kf : CEnvLay D (D.params f)} {cargs : List CX}
    (hF : FnCorr X.EL X.R X.CR f fc ps Kf) (hA : ArgsTo X K args cargs ps Kf) :
    StmtCorr X m K (Stmt.call (l := l) f args hp hr) (.call fc cargs none) := by
  intro σ st ρG ρC hc hrel hnf
  have hc' : corrW X.EL (σ.lese Λ args.orte) st := (corrW_lese _ _ _ _ _).mpr hc
  obtain ⟨vs, st1, ρ0, hev, hs, hb, hr0⟩ := hA _ st ρG ρC hc' hrel
  have hc1 := corrW_same hc' hs
  have hex : execStmt X.O X.passes X.R (Stmt.call (l := l) f args hp hr) σ ρG =
      match X.R f (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρG) with
      | .ok σ' _ => .ok σ' ρG
      | .grund _ r => keinGrund hr r
      | .logik e => .logik e
      | .hardware e => .hardware e := rfl
  rw [hex] at hnf ⊢
  cases hR : X.R f (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρG) with
  | ok σ' v =>
      obtain ⟨st2, rv, hcr, hro⟩ := hF _ st1 _ vs ρ0 hc1 hb hr0 (by rw [hR]; rfl)
      rw [hR] at hro
      exact ⟨_, Exec.call hev hcr rfl, st2, ρC, rfl, hro.1, hrel⟩
  | grund σ' r => exact (Nat.not_lt_zero r.val (by have := r.isLt; omega)).elim
  | logik e => rw [hR] at hnf; exact Bool.noConfusion hnf
  | hardware e => rw [hR] at hnf; exact Bool.noConfusion hnf

/-- M7. `T x = f(a, b);` (8744) -- the answer bound to a fresh local. -/
theorem bsem_bindCall (m : Nat) {V : Vertrag D} {l : Bool} {Λ' : List (Res D)} {τ : Ty}
    (f : D.Fn) (args : Args D Γ Λ (D.params f)) (he : D.erg f = some τ)
    (hp : RufPasst D V (D.signatur f) Λ) (hr : D.gruende f = 0)
    (rest : Block D V l (τ :: Γ) (nach D f Λ) Λ') {fc : Nat} {ps : List (Nat × CTy)}
    {Kf : CEnvLay D (D.params f)} {cargs : List CX} {x : Nat} {τc : CTy} {cr : CS}
    (hF : FnCorr X.EL X.R X.CR f fc ps Kf) (hA : ArgsTo X K args cargs ps Kf)
    (hK : K.okB = true) (hf : K.freshB x = true) (hd : declOk τ τc = true)
    (hrest : BlockSem X m (K.push τ x) rest cr) :
    BlockSem X m K (Block.bindCall f args he hp hr rest)
      (.seq (.call fc cargs (some (x, τc))) cr) := by
  intro σ st ρG ρC hc hrel hnf
  have hc' : corrW X.EL (σ.lese Λ args.orte) st := (corrW_lese _ _ _ _ _).mpr hc
  obtain ⟨vs, st1, ρ0, hev, hs, hb, hr0⟩ := hA _ st ρG ρC hc' hrel
  have hc1 := corrW_same hc' hs
  have hex : execBlock X.O X.passes X.R (Block.bindCall f args he hp hr rest) σ ρG =
      match X.R f (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρG) with
      | .ok σ' v => (execBlock X.O X.passes X.R rest σ' (.cons (ergWert he v) ρG)).schrumpf
      | .grund _ r => keinGrund hr r
      | .logik e => .logik e
      | .hardware e => .hardware e := rfl
  rw [hex] at hnf ⊢
  cases hR : X.R f (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρG) with
  | ok σ' v =>
      rw [hR] at hnf
      obtain ⟨st2, rv, hcr, hro⟩ := hF _ st1 _ vs ρ0 hc1 hb hr0 (by rw [hR]; rfl)
      rw [hR] at hro
      obtain ⟨hc2, hret⟩ := hro
      obtain ⟨c, hrv, hvc⟩ := retCorr_ergWert he v rv hret
      subst hrv
      have hput : putDst (some (x, τc)) (some c) ρC = some (lokUpd ρC x c) := by
        simp only [putDst, convV_of_valCorr hvc hd]
      have hr1 := envRel_push hK hf hrel _ c hvc
      rw [istFehler_schrumpf] at hnf
      obtain ⟨o, h2, hO⟩ := hrest σ' st2 _ (lokUpd ρC x c) hc2 hr1 hnf
      exact ⟨o, Exec.seqN (Exec.call hev hcr hput) h2, stOut_schrumpf X m _ o hO⟩
  | grund σ' r => exact (Nat.not_lt_zero r.val (by have := r.isLt; omega)).elim
  | logik e => rw [hR] at hnf; exact Bool.noConfusion hnf
  | hardware e => rw [hR] at hnf; exact Bool.noConfusion hnf

end Ruf

theorem corrW_foldl_lese {EL : EmitLay D} {st : CSt} {α : Type} (g : α → List (Res D))
    (h : α → List (D.Tab ⊕ D.Glob)) :
    ∀ (xs : List α) (σ : World D),
      corrW EL (xs.foldl (fun σ' i => σ'.lese (g i) (h i)) σ) st ↔ corrW EL σ st
  | [], _ => Iff.rfl
  | a :: xs, σ => (corrW_foldl_lese g h xs (σ.lese (g a) (h a))).trans Iff.rfl

/-- Frames touch only stack blocks: the memory relation does not see them. -/
theorem corrW_enterFrame {EL : EmitLay D} {σ : World D} {st : CSt} (fr : Nat) (xs : List Nat)
    (h : corrW EL σ st) : corrW EL σ (enterFrame st fr xs) := h

theorem corrW_leaveFrame {EL : EmitLay D} {σ : World D} {st : CSt} (fr : Nat)
    (h : corrW EL σ st) : corrW EL σ (leaveFrame st fr) := h

/-- M7, THE CALL: `rufAt` at depth `n + 1` against `CallAt` at depth
    `n + 1`, from the correspondence of the callee's body (in frame
    `n + 1`, with its own callees at depth `n`). The requires, ensures and
    invariant clauses are logic: they are checked by the model, not
    emitted, and a failing one is an error outcome. Entering and leaving
    the frame touch only stack blocks. -/
theorem cCorr_ruf (EL : EmitLay D) (orc : DevOrc) (XR : CCallR) (P : Programm D) (O : Orakel D)
    (passes n : Nat) (Pr : CProg) (f : D.Fn) (fc : Nat) (F : CFun) (hPr : Pr fc = some F)
    (Kf : CEnvLay D (D.params f)) (m : Nat)
    (hbody : EndSem ⟨EL, orc, n + 1, CallAt EL.lay orc XR Pr n, XR, O, passes,
      rufAt P O passes n⟩ m true Kf (P.rumpf f) F.body) :
    FnCorr EL (rufAt P O passes (n + 1)) (CallAt EL.lay orc XR Pr (n + 1)) f fc F.params Kf := by
  intro σ st ρG vs ρ0 hc hb hr hnf
  simp only [rufAt] at hnf ⊢
  by_cases hq : wahr? (eval (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte)
      (P.requires f) (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte) ρG) = false
  · rw [if_pos hq] at hnf; exact Bool.noConfusion hnf
  rw [if_neg hq] at hnf ⊢
  have hc1 : corrW EL (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte)
      (enterFrame st (n + 1) F.locals) := corrW_enterFrame (n + 1) F.locals hc
  cases hE : execEnd (V := vertragVon D f) O passes (rufAt P O passes n) (P.rumpf f)
      (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte) ρG with
  | zurueck σ' v =>
      rw [hE] at hnf
      obtain ⟨o, hx, hO⟩ := hbody _ _ ρG ρ0 hc1 hr (by rw [hE]; rfl)
      rw [hE] at hO
      obtain ⟨st1, hc2, hret⟩ := hO
      dsimp only at hnf ⊢
      by_cases hens : wahr? (eval (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte)
          (P.ensures f) (σ'.lese (vertragVon D f).ende (P.ensures f).orte)
          (ergEnv (D.erg f) v ρG)) = false
      · rw [if_pos hens] at hnf; exact Bool.noConfusion hnf
      rw [if_neg hens] at hnf ⊢
      cases hfind : D.invs.find? (fun i => schuldet f i &&
          !wahr? (eval ((D.invs.filter (schuldet f)).foldl
            (fun σ' i => σ'.lese (invSicht D i) (P.invariante i).orte)
            (σ'.lese (vertragVon D f).ende (P.ensures f).orte)) (P.invariante i)
            ((D.invs.filter (schuldet f)).foldl
            (fun σ' i => σ'.lese (invSicht D i) (P.invariante i).orte)
            (σ'.lese (vertragVon D f).ende (P.ensures f).orte)) .nil)) with
      | some i => rw [hfind] at hnf; exact Bool.noConfusion hnf
      | none =>
          have hc3 : corrW EL ((D.invs.filter (schuldet f)).foldl
              (fun σ' i => σ'.lese (invSicht D i) (P.invariante i).orte)
              (σ'.lese (vertragVon D f).ende (P.ensures f).orte)) (leaveFrame st1 (n + 1)) :=
            (corrW_foldl_lese _ _ _ _).mpr ((corrW_lese _ _ _ _ _).mpr (corrW_leaveFrame _ hc2))
          rcases hret with ⟨cv, ho, hrc⟩ | ⟨-, hV, ρ1, ho⟩
          · exact ⟨_, cv, ⟨F, ρ0, o, hPr, hb, hx, st1, Or.inl ho, rfl⟩, hc3, hrc⟩
          · exact ⟨_, none, ⟨F, ρ0, o, hPr, hb, hx, st1, Or.inr ⟨rfl, ρ1, ho⟩, rfl⟩, hc3,
              retCorr_none hV v⟩
  | grund σ' r =>
      obtain ⟨o, -, hO⟩ := hbody _ _ ρG ρ0 hc1 hr (by rw [hE]; rfl)
      rw [hE] at hO
      exact hO.elim
  | leave h _ _ => exact absurd h (by decide)
  | next h _ _ => exact absurd h (by decide)
  | logik e => rw [hE] at hnf; exact Bool.noConfusion hnf
  | hardware e => rw [hE] at hnf; exact Bool.noConfusion hnf

/-! ## 7. M8: `locks`, and foreign calls without effect -/

/-- A foreign call without arguments that returns and changes no memory:
    the ASSUMPTION at `L_nimm()`/`L_gib()` (runtime functions whose
    bodies the emitter does not write; `CS.ext`). -/
def ExtNoop (XR : CCallR) (n : Nat) : Prop :=
  ∀ st : CSt, ∃ st', XR n st [] st' none ∧ SameML st st'

section Sperre

variable (X : TVCtx D) {Γ : Ctx} {Λ : List (Res D)} (K : CEnvLay D Γ)

theorem exec_extNoop {n : Nat} (hx : ExtNoop X.XR n) (st : CSt) (ρ : CLok) :
    ∃ st', Exec X.EL.lay X.orc X.fr X.CR X.XR (.ext n [] none) st ρ (.norm st' ρ) ∧
      SameML st st' := by
  obtain ⟨st', h1, h2⟩ := hx st
  exact ⟨st', Exec.ext rfl h1 rfl, h2⟩

/-- M8. A release before a statement (`L_gib(); return;`, emitted for every
    open lock before `return` and `goto`, 8182/9232) keeps the statement's
    correspondence. -/
theorem scorr_extPre (m : Nat) {V : Vertrag D} {l : Bool} {Λ' : List (Res D)}
    {s : Stmt D V l Γ Λ Λ'} {cs : CS} (n : Nat) (hx : ExtNoop X.XR n)
    (hs : StmtCorr X m K s cs) : StmtCorr X m K s (.seq (.ext n [] none) cs) := by
  intro σ st ρG ρC hc hr hnf
  obtain ⟨st1, h1, hs1⟩ := exec_extNoop X hx st ρC
  obtain ⟨o, h2, hO⟩ := hs σ st1 ρG ρC (corrW_same hc hs1) hr hnf
  exact ⟨o, Exec.seqN h1 h2, hO⟩

theorem istFehler_mapWelt {V : Vertrag D} {l : Bool} {Γ' : Ctx} (g : World D → World D)
    (a : Ausgang V l Γ') : (a.mapWelt g).istFehler = a.istFehler := by
  cases a <;> rfl

/-- M8. `L_nimm(); { body } L_gib();` (9175/9181). Taking and giving the
    lock change only Gabbro's trace, and the two runtime calls change no
    memory; the body corresponds as a block. -/
theorem scorr_locks (m : Nat) {V : Vertrag D} {l : Bool} (L : D.Lock)
    (hr : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang L)
    (body : Block D V l Γ (.held L :: Λ) (.held L :: Λ)) {cb : CS} (nimm gib : Nat)
    (hN : ExtNoop X.XR nimm) (hG : ExtNoop X.XR gib) (hb : BlockSem X m K body cb) :
    StmtCorr X m K (Stmt.locks L hr body) (.seq (.ext nimm [] none) (.seq cb (.ext gib [] none))) := by
  intro σ st ρG ρC hc hrel hnf
  have hex : execStmt X.O X.passes X.R (Stmt.locks L hr body) σ ρG =
      (execBlock X.O X.passes X.R body (σ.nimmt L) ρG).mapWelt (·.gibt L) := rfl
  rw [hex, istFehler_mapWelt] at hnf
  rw [hex]
  obtain ⟨st1, h1, hs1⟩ := exec_extNoop X hN st ρC
  have hc1 : corrW X.EL (σ.nimmt L) st1 := corrW_same hc hs1
  obtain ⟨o, h2, hO⟩ := hb _ st1 ρG ρC hc1 hrel hnf
  cases hB : execBlock X.O X.passes X.R body (σ.nimmt L) ρG with
  | ok σ' ρ' =>
      rw [hB] at hO
      obtain ⟨st2, ρC2, ho, hc2, hr2⟩ := hO
      subst ho
      obtain ⟨st3, h3, hs3⟩ := exec_extNoop X hG st2 ρC2
      exact ⟨_, Exec.seqN h1 (Exec.seqN h2 h3), st3, ρC2, rfl,
        (corrW_same hc2 hs3 : corrW X.EL (σ'.gibt L) st3), hr2⟩
  | zurueck σ' v =>
      rw [hB] at hO
      obtain ⟨st2, cv, ho, hc2, hrc⟩ := hO
      subst ho
      exact ⟨_, Exec.seqN h1 (Exec.seqX h2 rfl), st2, cv, rfl,
        (hc2 : corrW X.EL (σ'.gibt L) st2), hrc⟩
  | grund σ' r => rw [hB] at hO; exact hO.elim
  | leave hl σ' ρ' =>
      rw [hB] at hO
      obtain ⟨st2, ρC2, ho, hc2, hr2⟩ := hO
      subst ho
      exact ⟨_, Exec.seqN h1 (Exec.seqX h2 rfl), st2, ρC2, rfl,
        (hc2 : corrW X.EL (σ'.gibt L) st2), hr2⟩
  | next hl σ' ρ' =>
      rw [hB] at hO
      obtain ⟨st2, ρC2, ho, hc2, hr2⟩ := hO
      subst ho
      exact ⟨_, Exec.seqN h1 (Exec.seqX h2 rfl), st2, ρC2, rfl,
        (hc2 : corrW X.EL (σ'.gibt L) st2), hr2⟩
  | logik e => rw [hB] at hnf; exact Bool.noConfusion hnf
  | hardware e => rw [hB] at hnf; exact Bool.noConfusion hnf

/-! ## 8. M9: `match` on an option -/

/-- The emitted option match (10970ff.):
    `{ uint32_t _o = e; if (_o != T_NONE) { uint32_t x = _o; p } else { a } }`,
    with `T_NONE` the sentinel `n` (`#define T_NONE (N)`, 3638). -/
def CS.optMatch (o x : Nat) (ce : CX) (n : Int) (cp ca : CS) : CS :=
  .seq (.set o CIT.u32.ty ce)
    (.ite (.cmp .ne CIT.u32 (.var o) (.lit n)) (.seq (.set x CIT.u32.ty (.var o)) cp) ca)

/-- M9. The option match against `onOption`. -/
theorem scorr_onOption (m : Nat) {V : Vertrag D} {l : Bool} {Λ' : List (Res D)} {n : Int}
    {oe : Expr D Γ Λ (.opt n)} {p : Block D V l (.index n :: Γ) Λ Λ'} {a : Block D V l Γ Λ Λ'}
    {ce : CX} {cp ca : CS} {o x : Nat} (hK : K.okB = true) (ho : K.freshB o = true)
    (hx : K.freshB x = true) (hn0 : 0 ≤ n) (hn : n ≤ CIT.u32.hi) (he : ExprCorr X K ce oe)
    (hp : BlockSem X m (K.push (.index n) x) p cp) (ha : BlockSem X m K a ca) :
    StmtCorr X m K (Stmt.onOption oe p a) (CS.optMatch o x ce n cp ca) := by
  intro σ st ρG ρC hc hrel hnf
  have hc' : corrW X.EL (σ.lese Λ oe.orte) st := (corrW_lese _ _ _ _ _).mpr hc
  obtain ⟨v, st1, h1, hv, hc1⟩ := he.run X K hc' hrel
  have hu32lo : CIT.u32.lo = 0 := rfl
  have hex : execStmt X.O X.passes X.R (Stmt.onOption oe p a) σ ρG =
      match eval (σ.lese Λ oe.orte) oe (σ.lese Λ oe.orte) ρG with
      | Option.some k => (execBlock X.O X.passes X.R p (σ.lese Λ oe.orte) (.cons k ρG)).schrumpf
      | Option.none => execBlock X.O X.passes X.R a (σ.lese Λ oe.orte) ρG := rfl
  rw [hex] at hnf ⊢
  have hr1 := envRel_upd_fresh hK ho hrel v
  cases hk : eval (σ.lese Λ oe.orte) oe (σ.lese Λ oe.orte) ρG with
  | some k =>
      rw [hk] at hnf
      have hvk : v = .int k.n := by rw [hk] at hv; exact hv
      subst hvk
      have k0 := k.lo_le
      have k1 := k.le_hi
      have hs1 : Exec X.EL.lay X.orc X.fr X.CR X.XR (.set o CIT.u32.ty ce) st ρC
          (.norm st1 (lokUpd ρC o (.int k.n))) :=
        Exec.set h1 (by
          show convV (.int false .w32) (.int k.n) = _
          simp only [convV]
          rw [show (⟨false, .w32⟩ : CIT) = CIT.u32 from rfl, conv_id ⟨by omega, by omega⟩])
      have hoval : (lokUpd ρC o (.int k.n)) o = .int k.n := by simp [lokUpd]
      have hcond : ev X.EL.lay X.orc X.fr (.cmp .ne CIT.u32 (.var o) (.lit n)) st1
          (lokUpd ρC o (.int k.n)) = some (.int (b2i (decide (k.n ≠ n))), st1) :=
        ev_cmp (ev_var hoval) rfl (conv_id ⟨by omega, by omega⟩) (conv_id ⟨by omega, hn⟩)
      have htr : truth (.int (b2i (decide (k.n ≠ n)))) = some true := by
        rw [decide_eq_true (show k.n ≠ n by omega)]; rfl
      have hsx : Exec X.EL.lay X.orc X.fr X.CR X.XR (.set x CIT.u32.ty (.var o)) st1
          (lokUpd ρC o (.int k.n)) (.norm st1 (lokUpd (lokUpd ρC o (.int k.n)) x (.int k.n))) :=
        Exec.set (ev_var hoval) (by
          show convV (.int false .w32) (.int k.n) = _
          simp only [convV]
          rw [show (⟨false, .w32⟩ : CIT) = CIT.u32 from rfl, conv_id ⟨by omega, by omega⟩])
      have hr2 := envRel_push (τ := .index n) hK hx hr1 (show Wert D (.index n) from k)
        (.int k.n) rfl
      rw [istFehler_schrumpf] at hnf
      obtain ⟨o', h2, hO⟩ := hp _ st1 _ _ hc1 hr2 hnf
      exact ⟨o', Exec.seqN hs1 (Exec.iteT hcond htr (Exec.seqN hsx h2)),
        stOut_schrumpf X m _ o' hO⟩
  | none =>
      rw [hk] at hnf
      have hvk : v = .int n := by rw [hk] at hv; exact hv
      subst hvk
      have hs1 : Exec X.EL.lay X.orc X.fr X.CR X.XR (.set o CIT.u32.ty ce) st ρC
          (.norm st1 (lokUpd ρC o (.int n))) :=
        Exec.set h1 (by
          show convV (.int false .w32) (.int n) = _
          simp only [convV]
          rw [show (⟨false, .w32⟩ : CIT) = CIT.u32 from rfl, conv_id ⟨by omega, hn⟩])
      have hoval : (lokUpd ρC o (.int n)) o = .int n := by simp [lokUpd]
      have hcond : ev X.EL.lay X.orc X.fr (.cmp .ne CIT.u32 (.var o) (.lit n)) st1
          (lokUpd ρC o (.int n)) = some (.int (b2i (decide (n ≠ n))), st1) :=
        ev_cmp (ev_var hoval) rfl (conv_id ⟨by omega, hn⟩) (conv_id ⟨by omega, hn⟩)
      have hfa : truth (.int (b2i (decide (n ≠ n)))) = some false := by
        rw [decide_eq_false (show ¬ (n ≠ n) by omega)]; rfl
      obtain ⟨o', h2, hO⟩ := ha _ st1 _ _ hc1 hr1 hnf
      exact ⟨o', Exec.seqN hs1 (Exec.iteF hcond hfa h2), hO⟩

end Sperre

/-! ## 9. M10: a by-value struct local -/

/-- M10. `T x = (T){ .f = v, … };` then `x.f`: a by-value struct local is a
    stack block of the frame with the record's layout; a field store
    writes exactly its cell (the other fields and every other object keep
    their contents), and the field load reads it back. The Lean grammar
    has no local records (a record value is a count-1 table there,
    Zucker's `verbund`), so this form has a semantics and no Gabbro
    counterpart. -/
theorem structLocal_rw (L : CLayout) (orc : DevOrc) (fr : Nat) (CR XR : CCallR) (x : Nat)
    (R : RecLay) (hR : R.wf = true) (h1 : R.count = 1)
    (hL : L (.stk fr x) = some { lay := R, kind := .plain, base := 0 }) (st : CSt)
    (hlive : st.live (.stk fr x) = true) (j : Nat) (hj : j < R.nf) (n : Int)
    (hfit : valFits (R.fty j) (.int n) = true) (ρ : CLok) :
    ∃ st', Exec L orc fr CR XR (.store (.fld (.addrL x) (R.off j)) (R.fty j) (.lit n)) st ρ
        (.norm st' ρ) ∧
      ev L orc fr (.ld (.fld (.addrL x) (R.off j)) (R.fty j)) st' ρ = some (.int n, st') ∧
      (∀ j', j' < R.nf → j' ≠ j → st'.mem (.stk fr x) (R.off j') = st.mem (.stk fr x) (R.off j')) ∧
      (∀ b o, b ≠ .stk fr x → st'.mem b o = st.mem b o) := by
  have hoff := RecLay.off_lt hR hj
  have hcell : R.cell (R.off j) = some (R.fty j) := by
    have := RecLay.cell_pos hR hj (k := 0) (by omega)
    simpa using this
  have hp : ptrAdd L ⟨.stk fr x, 0⟩ (R.off j : Int) 1 = some ⟨.stk fr x, (R.off j : Int)⟩ := by
    have e1 : (⟨.stk fr x, 0⟩ : CPtr).off + (R.off j : Int) * ((1 : Nat) : Int) = (R.off j : Int) := by
      show (0 : Int) + _ * ((1 : Nat) : Int) = _
      rw [Int.natCast_one, Int.mul_one, Int.zero_add]
    rw [ptrAdd_progress L _ _ 1 _ hL (by rw [e1]; omega)
      (by rw [e1]; show _ ≤ ((R.count * R.ssize : Nat) : Int); rw [h1]; omega)]
    rw [e1]
  have hfld : ev L orc fr (.fld (.addrL x) (R.off j)) st ρ = some (.ptr ⟨.stk fr x, (R.off j : Int)⟩, st) := by
    simp only [ev, hp]
  have hacc : ∀ (s : CSt) (md : AccMode), s.live (.stk fr x) = true → BKind.plain.permits md = true →
      accOk L s ⟨.stk fr x, (R.off j : Int)⟩ (R.fty j) md = true := by
    intro s md hl hm
    unfold accOk
    rw [show (⟨.stk fr x, (R.off j : Int)⟩ : CPtr).blk = .stk fr x from rfl, hL]
    dsimp only
    rw [hl, hm, show ((R.off j : Nat) : Int).toNat = R.off j from Int.toNat_natCast _, hcell]
    simp
  have hst := bStore_progress L st ⟨.stk fr x, (R.off j : Int)⟩ (R.fty j) (.int n)
    (hacc st .wr hlive rfl) hfit
  refine ⟨_, Exec.store hfld rfl (convV_of_valFits _ _ hfit) hst, ?_, ?_, ?_⟩
  · have hl' : ({ st with mem := memUpd st.mem (.stk fr x) (R.off j : Int).toNat (.int n) } : CSt).live
        (.stk fr x) = true := hlive
    have hld := bLoad_progress L { st with mem := memUpd st.mem (.stk fr x) (R.off j : Int).toNat (.int n) }
      ⟨.stk fr x, (R.off j : Int)⟩ (R.fty j) (hacc _ .rd hl' rfl) (by
        show memUpd st.mem (CBlk.stk fr x) (R.off j : Int).toNat (CVal.int n) (CBlk.stk fr x)
          (R.off j : Int).toNat ≠ CVal.undef
        rw [memUpd_same]; simp)
    have hfld' : ev L orc fr (.fld (.addrL x) (R.off j))
        { st with mem := memUpd st.mem (.stk fr x) (R.off j : Int).toNat (.int n) } ρ =
        some (.ptr ⟨.stk fr x, (R.off j : Int)⟩,
          { st with mem := memUpd st.mem (.stk fr x) (R.off j : Int).toNat (.int n) }) := by
      simp only [ev, hp]
    rw [ev_ld hfld' hld]
    show some (memUpd st.mem (CBlk.stk fr x) (R.off j : Int).toNat (CVal.int n) (CBlk.stk fr x)
      (R.off j : Int).toNat, _) = _
    rw [memUpd_same]
  · intro j' hj' hne
    show memUpd st.mem (.stk fr x) (R.off j : Int).toNat (.int n) (.stk fr x) (R.off j') = _
    apply memUpd_other
    intro hc
    obtain ⟨-, ho⟩ := hc
    rw [Int.toNat_natCast] at ho
    exact hne (RecLay.off_inj hR hj' hj ho)
  · intro b o hb
    show memUpd st.mem (.stk fr x) _ (.int n) b o = _
    exact memUpd_other _ _ _ _ _ _ (fun hc => hb hc.1)

/-! ## 10. M11: the `_Static_assert` prelude -/

/-- M11. Every unit's prelude (`KOPF`, 696ff.) pins two
    implementation-defined behaviours: `(-1 >> 1) == -1` (arithmetic right
    shift) and `(int)0xFFFFFFFFu == -1` (modular conversion). As
    compile-time facts they are assumptions about the C compiler; the
    model makes both STUCK (`OpUB.shiftNeg`, `ConvUB`), so no correspondence
    in T4 depends on them -- the prelude rules out a compiler on which the
    emitted code would mean something else, it does not feed a proof. -/
theorem prelude_pins :
    cArith .shr CIT.i32 (-1) 1 = none ∧ conv CIT.i32 4294967295 = none := by
  decide

/-- M11. `sizeof` of an emitted record is its layout's size; for the
    reference program's `Konto` the `_Static_assert(sizeof(…) > 0)` shape
    holds by computation (a certificate checks it per record). -/
theorem sizeof_konto : 0 < kontoLay.size ∧ kontoLay.ssize = 4 := by decide

/-
CUTS: what this pass does not do, by name.
- A CALL IS RELATED THROUGH `FnCorr`, and `cCorr_ruf` builds it for one
  depth from the callee body's correspondence one depth below: a
  recursive unit needs the certificate to supply the body correspondence
  at every depth it uses (Gabbro's `rufAt` fuel and C's `CallAt` depth
  are the same number, so the chains line up).
- ARGUMENT PASSING is the premise `ArgsTo`: the certificate shows that
  C's parameter passing (`bindParams`) establishes the callee's locals
  relation. A generic discharge for every argument shape is not given;
  the witness discharges it for `lies(k, i)` by computation.
- THE `or R` CHANNEL (`bool f(…, T *_wert, R *_grund)`, the call
  `if (!f(…, &x, &e)) { … }`, `*_grund = F; return false;`) is not
  covered: reason returns have no outcome relation yet (pass (i) CUTS),
  and the out-parameters `&x`, `&e` are the stack blocks of
  `CSpeicher.ausgabe_zeuge`, whose statement-level wiring is not done.
- `onGrund` (`switch` over a reason) and `onTag` (pass (iii)) are not
  covered; `CS.sw` has the semantics.
- `narrow` is not covered: the emitted form (8664ff.) keeps using the
  narrowed C local for the new Gabbro variable, so two Gabbro variables
  share one C local and the locals relation needs a non-injective layout.
- `pruefung` is not covered (no measured emitted shape was pinned).
- The lock runtime and every foreign call is an assumption (`ExtNoop`).
- `static const` tables and by-value struct locals have no Gabbro
  constructor; their lemmas are C-side facts.
-/

#print axioms ecorr_slotParam
#print axioms ecorr_durch
#print axioms scorr_assignSlotParam
#print axioms scorr_assignDurch
#print axioms ecorr_und
#print axioms ecorr_oder
#print axioms cond_max
#print axioms ev_sizeofQuot
#print axioms hiSlots_ev
#print axioms constTab_read
#print axioms ro_store_stuck
#print axioms scorr_call
#print axioms bsem_bindCall
#print axioms cCorr_ruf
#print axioms scorr_extPre
#print axioms scorr_locks
#print axioms scorr_onOption
#print axioms structLocal_rw
#print axioms prelude_pins
#print axioms sizeof_konto

end Gabbro.Grammatik
