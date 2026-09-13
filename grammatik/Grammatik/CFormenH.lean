/-
  File:      Grammatik/CFormenH.lean
  Subject:   T4 pass (iii): the hard forms -- jumps, atomics with their
             memory orders, the foreign step (syscall stub, `extern`) as an
             assumption boundary, byte views with their pointer arithmetic
             and helpers, device registers through the observation trace.

  THE FORMS OF THIS PASS (emit.rs shapes; the survey of 2026-09-13)
    H1  `goto m_ende;` / `goto m_weiter;`     leave / next      scorr_leave, scorr_next
        (and the loops that consume them: `CS.forC`, pass (i) S7)
    H2  `atomic_store_explicit(&A, w, o);`    publish           scorr_publish
    H3  `T x = atomic_load_explicit(&A, o);`  awaits            bsem_awaits
    H4  `ok = atomic_compare_exchange_strong_explicit(&A, &_cx, des, os, of);`
        with `_cx` an address-taken local     (exchange … when) cas_success, cas_failure
    H5  the syscall stub / an `extern` call: a foreign step whose effect
        is an assumption (`XR`), related to Gabbro's axiom oracle
                                              axiomCall         scorr_axiomCall
    H6  `gabbro_le32(v->bytes + K)` (LESER_C, inlined), the byte view's
        pointer arithmetic                    leseBytes 4       ecorr_le32
    H7  `((uint64_t)(i) < N ? buf[(uint64_t)(i)] : (__builtin_trap(), 0))`
        (`lese_bytes`, the bound-checked byte read)
                                              slot of a byte table  ecorr_byteGuard
    H8  `(volatile uint8_t *)(uintptr_t)BASE` and `+ K` (device base)
                                              (the handle)      ev_devReg
    H9  `T x = (*(volatile T *)(d->basis + K));`
                                              regLies           regLies_step
    H10 `(*(volatile T *)(d->basis + K)) = e;`
                                              regSchreib        regSchreib_step
  H9/H10 are stated with the device window's liveness as a premise: the
  judgements of pass (i) carry the memory relation `corrW`, which says
  nothing about device windows (they are not memory), so the two forms
  are per-step lemmas rather than `StmtCorr` (CUTS).
-/
import Grammatik.CFormenM

namespace Gabbro.Grammatik

variable {D : Deklaration}

section Sprung

variable (X : TVCtx D) {Γ : Ctx} {Λ : List (Res D)} (K : CEnvLay D Γ)

/-! ## 1. H1: the jumps -/

/-- H1. `leave` is `goto m_ende;` (9235), a jump right past loop `m`. -/
theorem scorr_leave (m : Nat) {V : Vertrag D} (h : true = true) :
    StmtCorr X m K (Stmt.leave (V := V) (Γ := Γ) (Λ := Λ) h) (.goto (.ende m)) := by
  intro σ st ρG ρC hc hr _
  exact ⟨_, Exec.goto, st, ρC, rfl, hc, hr⟩

/-- H1. `next` is `goto m_weiter;`, a jump to the end of loop `m`'s body. -/
theorem scorr_next (m : Nat) {V : Vertrag D} (h : true = true) :
    StmtCorr X m K (Stmt.next (V := V) (Γ := Γ) (Λ := Λ) h) (.goto (.weiter m)) := by
  intro σ st ρG ρC hc hr _
  exact ⟨_, Exec.goto, st, ρC, rfl, hc, hr⟩

/-! ## 2. H2/H3: `publishes` and `awaits` -/

/-- H2. `atomic_store_explicit(&A, w, o);` (8792) under the declared store
    order `o`: the same memory effect as Gabbro's `publish` (a write of
    `A`), plus exactly one observation carrying the order. The payload's
    visibility is the memory model (A10), not this lemma. -/
theorem scorr_publish (m : Nat) {V : Vertrag D} {l : Bool} (g : D.Glob) (hgg : D.ggeist g = false)
    (hat : D.atomar g = true) {e : Expr D Γ Λ (D.gtyp g)} {ce : CX} (payload : List D.Glob)
    (hpl : payload = D.nutzlast g) (hw : V.gschreibt g = true) (hL : gdarf D g Λ)
    (o : COrd) (ho : o.storeOk = true) (he : ExprCorr X K ce e) :
    StmtCorr X m K (Stmt.publish (l := l) g e payload hpl hw hL)
      (.astore (.addr (.glob (X.EL.gnr g))) (X.EL.gty g) o ce) := by
  intro σ st ρG ρC hc hr _
  have hc' : corrW X.EL (σ.lese Λ e.orte) st := (corrW_lese _ _ _ _ _).mpr hc
  obtain ⟨v, st1, h1, hv, hc1⟩ := he.run X K hc' hr
  have hve := valCorr_int_of_fits _ _ _ _ (X.EL.gty_fits g) hv
  subst hve
  obtain ⟨st2, hs, hc2, -⟩ := corr_schreibGlob_atomar X.EL _ st1 hc1 g hgg hat Λ
    (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρG) o ho
  refine ⟨.norm st2 ρC, Exec.astore (by simp only [ev]; rfl) h1
    (convV_of_valFits _ _ (encW_fits _ _ _ (X.EL.gty_fits g))) hs, ?_⟩
  exact ⟨st2, ρC, rfl, hc2, hr⟩

/-- H3. `T x = atomic_load_explicit(&A, o);` (8804) under the declared load
    order: the local gets the encoded global, one observation is appended;
    Gabbro's `awaits` sees the publication (or the memory model failed,
    `Hardware.sichtbarkeit`, an error outcome). -/
theorem bsem_awaits (m : Nat) {V : Vertrag D} {l : Bool} {Λ' : List (Res D)} (g : D.Glob)
    (hgg : D.ggeist g = false) (hat : D.atomar g = true) (payload : List D.Glob)
    (hpl : payload = D.nutzlast g) (hL : gdarf D g Λ)
    (rest : Block D V l (D.gtyp g :: Γ) Λ Λ') {x : Nat} {τc : CTy} {cr : CS} (o : COrd)
    (ho : o.loadOk = true) (hK : K.okB = true) (hf : K.freshB x = true)
    (hd : declOk (D.gtyp g) τc = true) (hrest : BlockSem X m (K.push (D.gtyp g) x) rest cr) :
    BlockSem X m K (Block.awaits g payload hpl hL rest)
      (.seq (.set x τc (.ald (.addr (.glob (X.EL.gnr g))) (X.EL.gty g) o)) cr) := by
  intro σ st ρG ρC hc hr hnf
  have hex : execBlock X.O X.passes X.R (Block.awaits g payload hpl hL rest) σ ρG =
      if X.O.sichtbar g σ then
        (execBlock X.O X.passes X.R rest (σ.lese Λ [.inr g])
          (.cons ((σ.lese Λ [.inr g]).globs g) ρG)).schrumpf
      else .hardware (.sichtbarkeit D.a10) := rfl
  rw [hex] at hnf ⊢
  by_cases hs : X.O.sichtbar g σ = true
  · rw [if_pos hs] at hnf ⊢
    rw [istFehler_schrumpf] at hnf
    have hl := corr_leseGlob_atomar X.EL σ st hc g hgg hat o ho
    have hld : ev X.EL.lay X.orc X.fr (.ald (.addr (.glob (X.EL.gnr g))) (X.EL.gty g) o) st ρC =
        some (.int (encW (D.gtyp g) (σ.globs g)),
          { st with obs := .ard (X.EL.globPtr g) o (encW (D.gtyp g) (σ.globs g)) :: st.obs }) := by
      simp only [ev]
      rw [show (⟨.glob (X.EL.gnr g), 0⟩ : CPtr) = X.EL.globPtr g from rfl, hl]
    have hv : ValCorr X.EL (D.gtyp g) (σ.globs g) (.int (encW (D.gtyp g) (σ.globs g))) :=
      valCorr_encW _ _ _ (X.EL.gty_fits g)
    have hc1 : corrW X.EL (σ.lese Λ [.inr g])
        { st with obs := .ard (X.EL.globPtr g) o (encW (D.gtyp g) (σ.globs g)) :: st.obs } := hc
    have hr1 := envRel_push hK hf hr _ _ hv
    obtain ⟨o', h2, hO⟩ := hrest _ _ _ _ hc1 hr1 hnf
    exact ⟨o', Exec.seqN (Exec.set hld (convV_of_valCorr hv hd)) h2, stOut_schrumpf X m _ o' hO⟩
  · rw [if_neg hs] at hnf; exact Bool.noConfusion hnf

end Sprung

/-! ## 3. H4: compare-exchange -/

/-- H4. `atomic_compare_exchange_strong_explicit(&A, &_cx, des, os, of)`
    against a related `_Atomic` global whose value is the expected one
    (`_cx` holds it): it succeeds, writes `des` with exactly one
    observation carrying both orders, leaves `_cx` alone, and the new state
    is related to Gabbro's write of `A` (the `exchange … when old(A) == e`
    lowering, 9158; Gabbro's `exchange` is a read-compute-write under A10). -/
theorem cas_success (EL : EmitLay D) (σ : World D) (st : CSt) (h : corrW EL σ st) (g : D.Glob)
    (hgg : D.ggeist g = false) (hat : D.atomar g = true) (Λ : List (Res D)) (v : Wert D (D.gtyp g))
    (os ofl : COrd) (hof : ofl.failOk = true) :
    ∃ st', aCas EL.lay st (EL.globPtr g) (EL.gty g) os ofl (encW (D.gtyp g) (σ.globs g))
        (encW (D.gtyp g) v) = some (true, encW (D.gtyp g) (σ.globs g), st') ∧
      corrW EL (σ.schreibGlob g Λ v) st' ∧
      st'.obs = .acas (EL.globPtr g) os ofl (encW (D.gtyp g) (σ.globs g)) (encW (D.gtyp g) v) true
        :: st.obs := by
  obtain ⟨hl, hc⟩ := h.2 g hgg
  have ha := EL.accOk_glob st g hl .atom (by rw [hat]; rfl)
  have hfit := encW_fits (D.gtyp g) (EL.gty g) v (EL.gty_fits g)
  obtain ⟨st2, hs, hc2, -⟩ := corr_schreibGlob_atomar EL σ st h g hgg hat Λ v .seqCst rfl
  have hst2 := aStore_mem hs
  refine ⟨CSt.mk (memUpd st.mem (.glob (EL.gnr g)) 0 (.int (encW (D.gtyp g) v))) st.live
      (.acas (EL.globPtr g) os ofl (encW (D.gtyp g) (σ.globs g)) (encW (D.gtyp g) v) true
        :: st.obs), ?_, ?_, rfl⟩
  · unfold aCas
    rw [ha, hof, hfit]
    show (match st.mem (.glob (EL.gnr g)) 0 with
      | .int cur => if cur = encW (D.gtyp g) (σ.globs g) then some (true, cur, _) else some (false, cur, _)
      | _ => none) = _
    rw [hc]
    dsimp only
    rw [if_pos rfl]
    rfl
  · have e : corrW EL (σ.schreibGlob g Λ v) st2 := hc2
    unfold corrW at e ⊢
    rw [hst2.1, hst2.2.1] at e
    exact e

/-- H4. The failing case: the global does not hold the expected value;
    the operation writes nothing and hands back the value seen (which the
    emitted code stores into `_cx`, an ordinary stack store); one
    observation. The relation is unchanged. -/
theorem cas_failure (EL : EmitLay D) (σ : World D) (st : CSt) (h : corrW EL σ st) (g : D.Glob)
    (hgg : D.ggeist g = false) (hat : D.atomar g = true) (exp : Int) (v : Wert D (D.gtyp g))
    (os ofl : COrd) (hof : ofl.failOk = true) (hne : encW (D.gtyp g) (σ.globs g) ≠ exp) :
    aCas EL.lay st (EL.globPtr g) (EL.gty g) os ofl exp (encW (D.gtyp g) v) =
      some (false, encW (D.gtyp g) (σ.globs g),
        CSt.mk st.mem st.live (.acas (EL.globPtr g) os ofl (encW (D.gtyp g) (σ.globs g))
          (encW (D.gtyp g) v) false :: st.obs)) ∧
    corrW EL σ (CSt.mk st.mem st.live (.acas (EL.globPtr g) os ofl (encW (D.gtyp g) (σ.globs g))
          (encW (D.gtyp g) v) false :: st.obs)) := by
  obtain ⟨hl, hc⟩ := h.2 g hgg
  have ha := EL.accOk_glob st g hl .atom (by rw [hat]; rfl)
  have hfit := encW_fits (D.gtyp g) (EL.gty g) v (EL.gty_fits g)
  refine ⟨?_, h⟩
  unfold aCas
  rw [ha, hof, hfit]
  show (match st.mem (.glob (EL.gnr g)) 0 with
    | .int cur => if cur = exp then some (true, cur, _) else some (false, cur, _)
    | _ => none) = _
  rw [hc]
  dsimp only
  rw [if_neg hne]

/-! ## 4. H5: the foreign step (syscall stub, `extern`) -/

/-- THE ASSUMPTION BOUNDARY at a foreign call `n` for axiom `a`: from
    related states and arguments that establish the axiom's parameter
    relation, the foreign C code returns, and its state is related to the
    world the Gabbro oracle `O.wirkt` answers. With `GutO` (Satz.lean) the
    Gabbro side keeps the declared frame (`aschreibt`/`agschreibt`); this
    relation carries it over. It is named, not proved: the syscall stub's
    body is `asm` (`syscall_stumpf`, 7330). -/
def AxCorr (EL : EmitLay D) (O : Orakel D) (XR : CCallR) (a : D.Ax) (n : Nat)
    (ps : List (Nat × CTy)) (Ka : CEnvLay D (D.aparams a)) : Prop :=
  ∀ (σ : World D) (st : CSt) (ρA : Env D (D.aparams a)) (vs : List CVal) (ρ0 : CLok),
    corrW EL σ st → bindParams ps vs = some ρ0 → EnvRel EL Ka ρA ρ0 →
    ∃ st' rv, XR n st vs st' rv ∧ corrW EL (O.wirkt a σ ρA).1 st'

section Fremd

variable (X : TVCtx D) {Γ : Ctx} {Λ : List (Res D)} (K : CEnvLay D Γ)

/-- H5. A foreign call without an answer (`axiomCall`) against the emitted
    call of the stub. -/
theorem scorr_axiomCall (m : Nat) {V : Vertrag D} {l : Bool} (a : D.Ax)
    (args : Args D Γ Λ (D.aparams a)) (h : D.aerg a = none)
    (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
    (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
    (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
    (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ) {n : Nat} {ps : List (Nat × CTy)}
    {Ka : CEnvLay D (D.aparams a)} {cargs : List CX} (hax : AxCorr X.EL X.O X.XR a n ps Ka)
    (hA : ArgsTo X K args cargs ps Ka) :
    StmtCorr X m K (Stmt.axiomCall (l := l) a args h hw hg hd hgd) (.ext n cargs none) := by
  intro σ st ρG ρC hc hr hnf
  have hc' : corrW X.EL (σ.lese Λ args.orte) st := (corrW_lese _ _ _ _ _).mpr hc
  obtain ⟨vs, st1, ρ0, hev, hs, hb, hr0⟩ := hA _ st ρG ρC hc' hr
  obtain ⟨st2, rv, hx, hc2⟩ := hax _ st1 _ vs ρ0 (corrW_same hc' hs) hb hr0
  have hex : execStmt X.O X.passes X.R (Stmt.axiomCall (l := l) a args h hw hg hd hgd) σ ρG =
      match axiomAntwort X.O a (σ.lese Λ args.orte)
          (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρG) with
      | (σ', Option.some _) => .ok σ' ρG
      | (_, Option.none) => .hardware (.annahme a) := rfl
  rw [hex] at hnf ⊢
  have hant : axiomAntwort X.O a (σ.lese Λ args.orte)
      (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρG) =
      ((X.O.wirkt a (σ.lese Λ args.orte)
        (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρG)).1,
       einpassenErg (D.aerg a) (X.O.wirkt a (σ.lese Λ args.orte)
        (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρG)).2) := rfl
  rw [hant] at hnf ⊢
  cases hE : einpassenErg (D.aerg a) (X.O.wirkt a (σ.lese Λ args.orte)
      (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρG)).2 with
  | some _ =>
      exact ⟨_, Exec.ext hev hx rfl, st2, ρC, rfl, hc2, hr⟩
  | none => rw [hE] at hnf; exact Bool.noConfusion hnf

end Fremd

/-! ## 5. H6/H7: byte views -/

/-- `p[j]` on a byte pointer: `*(p + j)`, a `uint8_t` cell. -/
def byteAt (p : CX) (j : Int) : CX := .ld (.padd p (.lit j)) (.int false .w8)

/-- The return expression of `gabbro_le32` (LESER_C, 5591), with `p` its
    argument: `(uint32_t)p[3] << 24 | (uint32_t)p[2] << 16 |
    (uint32_t)p[1] << 8 | p[0]` (`|` groups to the left; `p[0]` is
    promoted and converted to `uint32_t`). -/
def le32 (p : CX) : CX :=
  .bin .bor CIT.u32
    (.bin .bor CIT.u32
      (.bin .bor CIT.u32
        (.bin .shl CIT.u32 (.cast CIT.u32 (byteAt p 3)) (.lit 24))
        (.bin .shl CIT.u32 (.cast CIT.u32 (byteAt p 2)) (.lit 16)))
      (.bin .shl CIT.u32 (.cast CIT.u32 (byteAt p 1)) (.lit 8)))
    (byteAt p 0)

theorem u32_hi : CIT.u32.hi = 4294967295 := by decide

theorem shl_byte (b : Nat) (hb : b < 256) (k m : Nat) (hkm : 2 ^ k = m) (hm : m ≤ 16777216)
    (hk : k < 32) :
    cArith .shl CIT.u32 (b : Int) (k : Int) = some ((b * m : Nat) : Int) := by
  have hbits : (CIT.u32.bits : Int) = 32 := rfl
  have h32 : (2 : Int) ^ CIT.u32.w.bits = 4294967296 := by simp [CIT.u32, CWidth.bits]
  have hmi : (2 : Int) ^ k = (m : Int) := by rw [← hkm]; simp
  have hbm : b * m ≤ 255 * 16777216 := Nat.mul_le_mul (by omega) hm
  unfold cArith
  have c1 : 0 ≤ (k : Int) ∧ (k : Int) < (CIT.u32.bits : Int) ∧ 0 ≤ (b : Int) :=
    ⟨by omega, by rw [hbits]; omega, by omega⟩
  rw [if_pos c1, if_neg (show ¬ (CIT.u32.sgn = true) by decide)]
  refine congrArg some ?_
  rw [Int.toNat_natCast, hmi]
  have e2 : (b : Int) * (m : Int) = ((b * m : Nat) : Int) := by rw [Int.natCast_mul]
  rw [e2]
  apply cWrap_of_range
  · omega
  · rw [h32]
    omega

theorem bor_nat (x y : Nat) (hx : x ≤ 4294967295) (hy : y ≤ 4294967295) :
    cArith .bor CIT.u32 (x : Int) (y : Int) = some ((x ||| y : Nat) : Int) := by
  show (if 0 ≤ (x : Int) ∧ 0 ≤ (y : Int) then some (((x : Int).toNat ||| (y : Int).toNat : Nat) : Int)
    else none) = _
  rw [if_pos ⟨by omega, by omega⟩, Int.toNat_natCast, Int.toNat_natCast]

/-- The four bytes, OR-ed at their shifts, are the little-endian number:
    the shifted bytes have disjoint bits. -/
theorem lor_bytes (b0 b1 b2 b3 : Nat) (h0 : b0 < 256) (h1 : b1 < 256) (h2 : b2 < 256) :
    ((b3 * 16777216 ||| b2 * 65536) ||| b1 * 256) ||| b0 =
      b0 + 256 * (b1 + 256 * (b2 + 256 * b3)) := by
  have p24 : (2 : Nat) ^ 24 = 16777216 := by simp
  have p16 : (2 : Nat) ^ 16 = 65536 := by simp
  have p8 : (2 : Nat) ^ 8 = 256 := by simp
  have s1 : b3 * 16777216 ||| b2 * 65536 = b3 * 16777216 + b2 * 65536 := by
    have h := Nat.two_pow_add_eq_or_of_lt (i := 24) (b := b2 * 65536) (by rw [p24]; omega) b3
    rw [p24, Nat.mul_comm 16777216 b3] at h
    exact h.symm
  have s2 : (b3 * 16777216 + b2 * 65536) ||| b1 * 256 = b3 * 16777216 + b2 * 65536 + b1 * 256 := by
    have h := Nat.two_pow_add_eq_or_of_lt (i := 16) (b := b1 * 256) (by rw [p16]; omega)
      (b3 * 256 + b2)
    rw [p16] at h
    have e : b3 * 16777216 + b2 * 65536 = 65536 * (b3 * 256 + b2) := by omega
    rw [e]
    exact h.symm
  have s3 : (b3 * 16777216 + b2 * 65536 + b1 * 256) ||| b0 =
      b3 * 16777216 + b2 * 65536 + b1 * 256 + b0 := by
    have h := Nat.two_pow_add_eq_or_of_lt (i := 8) (b := b0) (by rw [p8]; omega)
      (b3 * 65536 + b2 * 256 + b1)
    rw [p8] at h
    have e : b3 * 16777216 + b2 * 65536 + b1 * 256 = 256 * (b3 * 65536 + b2 * 256 + b1) := by
      omega
    rw [e]
    exact h.symm
  rw [s1, s2, s3]
  omega

/-- H6, the helper as a function: four byte cells that load `b0 … b3`
    make `le32` the little-endian number, without effect. -/
theorem ev_le32 {L : CLayout} {orc : DevOrc} {fr : Nat} (p : CX) (st : CSt) (ρ : CLok)
    (b0 b1 b2 b3 : Nat) (h0 : b0 < 256) (h1 : b1 < 256) (h2 : b2 < 256) (h3 : b3 < 256)
    (e0 : ev L orc fr (byteAt p 0) st ρ = some (.int b0, st))
    (e1 : ev L orc fr (byteAt p 1) st ρ = some (.int b1, st))
    (e2 : ev L orc fr (byteAt p 2) st ρ = some (.int b2, st))
    (e3 : ev L orc fr (byteAt p 3) st ρ = some (.int b3, st)) :
    ev L orc fr (le32 p) st ρ =
      some (.int ((b0 + 256 * (b1 + 256 * (b2 + 256 * b3)) : Nat) : Int), st) := by
  have cv : ∀ n : Nat, n ≤ 4294967295 → conv CIT.u32 (n : Int) = some (n : Int) :=
    fun n hn => conv_id ⟨by show (0 : Int) ≤ _; omega, by rw [u32_hi]; omega⟩
  have c24 : conv CIT.u32 24 = some 24 := cv 24 (by decide)
  have c16 : conv CIT.u32 16 = some 16 := cv 16 (by decide)
  have c8 : conv CIT.u32 8 = some 8 := cv 8 (by decide)
  have l24 : ev L orc fr (.lit 24) st ρ = some (.int 24, st) := rfl
  have l16 : ev L orc fr (.lit 16) st ρ = some (.int 16, st) := rfl
  have l8 : ev L orc fr (.lit 8) st ρ = some (.int 8, st) := rfl
  have q24 : (2 : Nat) ^ 24 = 16777216 := by simp
  have q16 : (2 : Nat) ^ 16 = 65536 := by simp
  have q8 : (2 : Nat) ^ 8 = 256 := by simp
  have x3 := ev_bin (op := .shl) (t := CIT.u32) (ev_cast CIT.u32 e3 (cv b3 (by omega))) l24
    (cv b3 (by omega)) c24 (shl_byte b3 h3 24 16777216 q24 (by omega) (by omega))
  have x2 := ev_bin (op := .shl) (t := CIT.u32) (ev_cast CIT.u32 e2 (cv b2 (by omega))) l16
    (cv b2 (by omega)) c16 (shl_byte b2 h2 16 65536 q16 (by omega) (by omega))
  have x1 := ev_bin (op := .shl) (t := CIT.u32) (ev_cast CIT.u32 e1 (cv b1 (by omega))) l8
    (cv b1 (by omega)) c8 (shl_byte b1 h1 8 256 q8 (by omega) (by omega))
  have o1 : b3 * 16777216 ||| b2 * 65536 ≤ 4294967295 := by
    have h := lor_bytes 0 0 b2 b3 (by decide) (by decide) h2
    rw [Nat.zero_mul, Nat.or_zero, Nat.or_zero] at h
    rw [h]
    have : b2 + 256 * b3 ≤ 65535 := by omega
    have : 256 * (b2 + 256 * b3) ≤ 256 * 65535 := Nat.mul_le_mul_left _ this
    have : 256 * (0 + 256 * (b2 + 256 * b3)) ≤ 256 * (256 * 65535) := by
      rw [Nat.zero_add]; exact Nat.mul_le_mul_left _ this
    exact Nat.le_trans (by rw [Nat.zero_add]; exact this) (by decide)
  have o2 : (b3 * 16777216 ||| b2 * 65536) ||| b1 * 256 ≤ 4294967295 := by
    have h := lor_bytes 0 b1 b2 b3 (by decide) h1 h2
    rw [Nat.or_zero] at h
    rw [h]
    have : b1 + 256 * (b2 + 256 * b3) ≤ 16777215 := by omega
    have : 256 * (b1 + 256 * (b2 + 256 * b3)) ≤ 256 * 16777215 := Nat.mul_le_mul_left _ this
    exact Nat.le_trans (by rw [Nat.zero_add]; exact this) (by decide)
  have p24 : b3 * 16777216 ≤ 4294967295 :=
    Nat.le_trans (Nat.mul_le_mul_right 16777216 (Nat.le_of_lt_succ h3)) (by decide)
  have p16 : b2 * 65536 ≤ 4294967295 :=
    Nat.le_trans (Nat.mul_le_mul_right 65536 (Nat.le_of_lt_succ h2)) (by decide)
  have p8 : b1 * 256 ≤ 4294967295 :=
    Nat.le_trans (Nat.mul_le_mul_right 256 (Nat.le_of_lt_succ h1)) (by decide)
  have p0 : b0 ≤ 4294967295 := Nat.le_trans (Nat.le_of_lt h0) (by decide)
  have y1 := ev_bin (op := .bor) (t := CIT.u32) x3 x2 (cv _ p24) (cv _ p16)
    (bor_nat _ _ p24 p16)
  have y2 := ev_bin (op := .bor) (t := CIT.u32) y1 x1 (cv _ o1) (cv _ p8) (bor_nat _ _ o1 p8)
  have y3 := ev_bin (op := .bor) (t := CIT.u32) y2 e0 (cv _ o2) (cv b0 p0)
    (bor_nat _ _ o2 p0)
  rw [lor_bytes b0 b1 b2 b3 h0 h1 h2] at y3
  exact y3

/-- A Gabbro byte field's encoding is the byte. -/
theorem encW_byte : ∀ {τ : Ty} (h : τ = .int 0 255) (v : Wert D τ),
    encW τ v = (cast (congrArg (Wert D) h) v : Zahl 0 255).n := by
  intro τ h v
  subst h
  rfl

section Bytes

variable (X : TVCtx D) {Γ : Ctx} {Λ : List (Res D)} (K : CEnvLay D Γ)

/-- The byte carrier's cell `k` through a pointer to its object plus `k`. -/
theorem byteAt_carrier (t : D.Tab) (f : D.Feld t) (hgt : D.geist t = false)
    (hss : (X.EL.trec t).ssize = 1) (hoff : (X.EL.trec t).off (X.EL.fnr t f) = 0)
    (hty : X.EL.slotTy t f = .int false .w8) (σ : World D) (st : CSt) (hc : corrW X.EL σ st)
    (ρC : CLok) (p : CX) (Kc : Int) (hK0 : 0 ≤ Kc)
    (hp : ev X.EL.lay X.orc X.fr p st ρC = some (.ptr ⟨.tab (X.EL.tnr t), Kc⟩, st))
    (j : Int) (hj0 : 0 ≤ j) (hj : Kc + j < D.count t) :
    ev X.EL.lay X.orc X.fr (byteAt p j) st ρC =
      some (.int (encW (D.typ t f) (σ.slots t (Kc + j) f)), st) := by
  have hcnt := X.EL.trec_count t
  have hsz : (X.EL.trec t).size = (X.EL.trec t).count := by
    show (X.EL.trec t).count * (X.EL.trec t).ssize = _
    rw [hss, Nat.mul_one]
  have hpa : ptrAdd X.EL.lay ⟨.tab (X.EL.tnr t), Kc⟩ j 1 = some (X.EL.slotPtr t (Kc + j) f) := by
    rw [ptrAdd_progress X.EL.lay _ _ 1 _ (X.EL.lay_tab t) (by show 0 ≤ Kc + j * ((1 : Nat) : Int); omega)
      (by show Kc + j * ((1 : Nat) : Int) ≤ (((X.EL.trec t).size : Nat) : Int); rw [hsz]; omega)]
    simp only [EmitLay.slotPtr, hss, hoff, Nat.mul_one, Nat.add_zero]
    congr 2
    show Kc + j * ((1 : Nat) : Int) = ((Kc + j).toNat : Int)
    omega
  have hl := corr_leseSlot X.EL σ st hc t hgt (Kc + j) f (by omega) (by omega)
  rw [hty] at hl
  have hpj : ev X.EL.lay X.orc X.fr (.padd p (.lit j)) st ρC =
      some (.ptr (X.EL.slotPtr t (Kc + j) f), st) := by
    simp only [ev, hp, hpa]
  exact ev_ld hpj hl

/-- H6. `gabbro_le32(p + K)` with `p` pointing to a byte carrier (the byte
    view's `v->bytes`): the Gabbro reading `leseBytes t f 4 K` (four
    bytes, little endian). Stated at a program point: `p` evaluates to the
    carrier's object in this state. -/
theorem le32_corr_at (t : D.Tab) (f : D.Feld t) (hf : D.typ t f = .int 0 255)
    (hgt : D.geist t = false) (hss : (X.EL.trec t).ssize = 1)
    (hoff : (X.EL.trec t).off (X.EL.fnr t f) = 0) (hty : X.EL.slotTy t f = .int false .w8)
    (Kc : Nat) (hhi : (Kc : Int) + 4 ≤ D.count t) (hL : darf D t Λ) (σ : World D) (st : CSt)
    (hc : corrW X.EL σ st) (ρG : Env D Γ) (ρC : CLok) (cp : CX)
    (hp : ev X.EL.lay X.orc X.fr cp st ρC = some (.ptr ⟨.tab (X.EL.tnr t), 0⟩, st)) :
    ev X.EL.lay X.orc X.fr (le32 (.padd cp (.lit Kc))) st ρC =
      some (.int (eval σ (Expr.leseBytes (Γ := Γ) t f hf 4 (Expr.lit (Kc : Int))
        (Int.natCast_nonneg Kc) (by omega) hL) σ ρG).n, st) := by
  have hcnt := X.EL.trec_count t
  have hsz : (X.EL.trec t).size = (X.EL.trec t).count := by
    show (X.EL.trec t).count * (X.EL.trec t).ssize = _
    rw [hss, Nat.mul_one]
  have hq : ev X.EL.lay X.orc X.fr (.padd cp (.lit Kc)) st ρC =
      some (.ptr ⟨.tab (X.EL.tnr t), (Kc : Int)⟩, st) := by
    have hpa : ptrAdd X.EL.lay ⟨.tab (X.EL.tnr t), 0⟩ (Kc : Int) 1 =
        some ⟨.tab (X.EL.tnr t), (Kc : Int)⟩ := by
      rw [ptrAdd_progress X.EL.lay _ _ 1 _ (X.EL.lay_tab t)
        (by show (0 : Int) ≤ 0 + (Kc : Int) * ((1 : Nat) : Int); omega)
        (by show (0 : Int) + (Kc : Int) * ((1 : Nat) : Int) ≤ (((X.EL.trec t).size : Nat) : Int)
            rw [hsz]; omega)]
      congr 2
      show (0 : Int) + (Kc : Int) * ((1 : Nat) : Int) = (Kc : Int)
      omega
    simp only [ev, hp, hpa]
  have gb : ∀ j : Int, 0 ≤ j → j < 4 →
      ev X.EL.lay X.orc X.fr (byteAt (.padd cp (.lit Kc)) j) st ρC =
        some (.int (encW (D.typ t f) (σ.slots t ((Kc : Int) + j) f)), st) :=
    fun j h0 h4 => byteAt_carrier X t f hgt hss hoff hty σ st hc ρC _ Kc (by omega) hq j h0 (by omega)
  -- the four bytes as naturals below 256
  have hb : ∀ k : Int, 0 ≤ encW (D.typ t f) (σ.slots t k f) ∧
      encW (D.typ t f) (σ.slots t k f) < 256 := by
    intro k
    rw [encW_byte hf]
    exact ⟨(cast (congrArg (Wert D) hf) (σ.slots t k f) : Zahl 0 255).lo_le,
      by have := (cast (congrArg (Wert D) hf) (σ.slots t k f) : Zahl 0 255).le_hi; omega⟩
  have nat_of : ∀ k : Int, encW (D.typ t f) (σ.slots t k f) =
      ((encW (D.typ t f) (σ.slots t k f)).toNat : Int) := fun k => by
    have := (hb k).1; omega
  have e0 := gb 0 (by decide) (by decide)
  have e1 := gb 1 (by decide) (by decide)
  have e2 := gb 2 (by decide) (by decide)
  have e3 := gb 3 (by decide) (by decide)
  rw [nat_of] at e0 e1 e2 e3
  have hv := ev_le32 (L := X.EL.lay) (orc := X.orc) (fr := X.fr) (.padd cp (.lit Kc)) st ρC _ _ _ _
    (by have := (hb ((Kc : Int) + 0)).2; omega) (by have := (hb ((Kc : Int) + 1)).2; omega)
    (by have := (hb ((Kc : Int) + 2)).2; omega) (by have := (hb ((Kc : Int) + 3)).2; omega)
    e0 e1 e2 e3
  rw [hv]
  congr 3
  -- the Gabbro side: `bytesZuZahl` of the four bytes from `Kc`
  show _ = bytesZuZahl (σ.bytesAb t f hf 4 (Kc : Int))
  simp only [World.bytesAb, bytesZuZahl]
  have r0 := (hb ((Kc : Int) + 0)).1
  have r1 := (hb ((Kc : Int) + 1)).1
  have r2 := (hb ((Kc : Int) + 2)).1
  have r3 := (hb ((Kc : Int) + 3)).1
  have t0 := Int.toNat_of_nonneg r0
  have t1 := Int.toNat_of_nonneg r1
  have t2 := Int.toNat_of_nonneg r2
  have t3 := Int.toNat_of_nonneg r3
  have q0 : encW (D.typ t f) (σ.slots t ((Kc : Int) + 0) f) =
      (cast (congrArg (Wert D) hf) (σ.slots t (Kc : Int) f) : Zahl 0 255).n := by
    rw [Int.add_zero]; exact encW_byte hf _
  have q1 : encW (D.typ t f) (σ.slots t ((Kc : Int) + 1) f) =
      (cast (congrArg (Wert D) hf) (σ.slots t ((Kc : Int) + 1) f) : Zahl 0 255).n :=
    encW_byte hf _
  have q2 : encW (D.typ t f) (σ.slots t ((Kc : Int) + 2) f) =
      (cast (congrArg (Wert D) hf) (σ.slots t ((Kc : Int) + 1 + 1) f) : Zahl 0 255).n := by
    rw [show (Kc : Int) + 1 + 1 = (Kc : Int) + 2 by omega]; exact encW_byte hf _
  have q3 : encW (D.typ t f) (σ.slots t ((Kc : Int) + 3) f) =
      (cast (congrArg (Wert D) hf) (σ.slots t ((Kc : Int) + 1 + 1 + 1) f) : Zahl 0 255).n := by
    rw [show (Kc : Int) + 1 + 1 + 1 = (Kc : Int) + 3 by omega]; exact encW_byte hf _
  rw [Int.natCast_add, Int.natCast_mul, Int.natCast_add, Int.natCast_mul, Int.natCast_add,
    Int.natCast_mul, t0, t1, t2, t3, q0, q1, q2, q3, Int.mul_zero, Int.add_zero]
  rfl

/-- H6. The same as a correspondence judgement, for a pointer expression
    that denotes the carrier in every related state (`PtrTo`: the named
    carrier, a pointer parameter). -/
theorem ecorr_le32 (t : D.Tab) (f : D.Feld t) (hf : D.typ t f = .int 0 255)
    (hgt : D.geist t = false) (hss : (X.EL.trec t).ssize = 1)
    (hoff : (X.EL.trec t).off (X.EL.fnr t f) = 0) (hty : X.EL.slotTy t f = .int false .w8)
    (Kc : Nat) (hhi : (Kc : Int) + 4 ≤ D.count t) (hL : darf D t Λ) {cp : CX}
    (hp : PtrTo X K cp t) :
    ExprCorr X K (le32 (.padd cp (.lit Kc)))
      (Expr.leseBytes t f hf 4 (Expr.lit (Kc : Int)) (Int.natCast_nonneg Kc) (by omega) hL) := by
  intro σ st ρG ρC hc hr
  exact ⟨_, st, le32_corr_at X t f hf hgt hss hoff hty Kc hhi hL σ st hc ρG ρC cp (hp st ρG ρC hr),
    rfl⟩


/-- Evaluation rule of an element address. -/
theorem ev_idx {L : CLayout} {orc : DevOrc} {fr : Nat} {p i : CX} {n es : Nat} {st st1 st2 : CSt}
    {ρ : CLok} {q q' : CPtr} {k : Int} (hp : ev L orc fr p st ρ = some (.ptr q, st1))
    (hi : ev L orc fr i st1 ρ = some (.int k, st2)) (hb : 0 ≤ k ∧ k < (n : Int))
    (hq : ptrAdd L q (k * es) 1 = some q') :
    ev L orc fr (.idx p i n es) st ρ = some (.ptr q', st2) := by
  simp only [ev, hp, hi, if_pos hb, hq]

/-- H7. The bound-checked byte read of `lese_bytes` (11190):
    `((uint64_t)(i) < N ? buf[(uint64_t)(i)] : (__builtin_trap(), 0))`
    over the carrier's storage `buf` (`N` its length): with the checker's
    bound the check passes, no trap, and the byte is the slot's. (The
    index is evaluated twice, as in the C text.) -/
theorem ecorr_byteGuard (t : D.Tab) (f : D.Feld t) (hf : D.typ t f = .int 0 255)
    (hgt : D.geist t = false) (hss : (X.EL.trec t).ssize = 1)
    (hoff : (X.EL.trec t).off (X.EL.fnr t f) = 0) (hty : X.EL.slotTy t f = .int false .w8)
    (hN : D.count t ≤ 2 ^ 64 - 1) {ci : CX} {i : Expr D Γ Λ (.index (D.count t))}
    (hL : darf D t Λ) (hi : ExprCorr X K ci i) :
    ExprCorr X K
      (.cond CIT.i32 (.cmp .lt CIT.u64 (.cast CIT.u64 ci) (.lit (D.count t)))
        (.ld (.idx (.addr (.tab (X.EL.tnr t))) (.cast CIT.u64 ci) (X.EL.trec t).count 1)
          (.int false .w8))
        .trap)
      (Expr.slot t f i hL) := by
  intro σ st ρG ρC hc hr
  obtain ⟨st1, h1, hc1⟩ := hi.runI X K hc hr
  obtain ⟨st2, h2, hc2⟩ := hi.runI X K hc1 hr
  have k0 := (eval σ i σ ρG).lo_le
  have k1 := (eval σ i σ ρG).le_hi
  have hcnt := X.EL.trec_count t
  have u64hi : CIT.u64.hi = 2 ^ 64 - 1 := by decide
  have ck : conv CIT.u64 (eval σ i σ ρG).n = some (eval σ i σ ρG).n :=
    conv_id ⟨by show (0 : Int) ≤ _; omega, by omega⟩
  have cN : conv CIT.u64 (D.count t) = some (D.count t) :=
    conv_id ⟨by show (0 : Int) ≤ _; omega, by omega⟩
  have hcmp := ev_cmp (op := .lt) (ev_cast CIT.u64 h1 ck)
    (rfl : ev X.EL.lay X.orc X.fr (.lit (D.count t)) st1 ρC = some (.int (D.count t), st1)) ck cN
  have htr : truth (.int (b2i (CCmp.lt.app (eval σ i σ ρG).n (D.count t)))) = some true := by
    show some (decide (b2i (decide ((eval σ i σ ρG).n < D.count t)) ≠ 0)) = some true
    rw [decide_eq_true (show (eval σ i σ ρG).n < D.count t by omega)]
    rfl
  have hsz : (X.EL.trec t).size = (X.EL.trec t).count := by
    show (X.EL.trec t).count * (X.EL.trec t).ssize = _
    rw [hss, Nat.mul_one]
  have hpa : ptrAdd X.EL.lay ⟨.tab (X.EL.tnr t), 0⟩ ((eval σ i σ ρG).n * ((1 : Nat) : Int)) 1 =
      some (X.EL.slotPtr t (eval σ i σ ρG).n f) := by
    have e1 : (⟨.tab (X.EL.tnr t), 0⟩ : CPtr).off + (eval σ i σ ρG).n * ((1 : Nat) : Int) *
        ((1 : Nat) : Int) = (eval σ i σ ρG).n := by
      show (0 : Int) + _ * ((1 : Nat) : Int) * ((1 : Nat) : Int) = _
      rw [Int.natCast_one, Int.mul_one, Int.mul_one, Int.zero_add]
    rw [ptrAdd_progress X.EL.lay _ _ 1 _ (X.EL.lay_tab t) (by rw [e1]; omega)
      (by rw [e1]; show _ ≤ (((X.EL.trec t).size : Nat) : Int); rw [hsz]; omega)]
    rw [e1]
    simp only [EmitLay.slotPtr, hss, hoff, Nat.mul_one, Nat.add_zero]
    rw [Int.toNat_of_nonneg k0]
  have hidx := ev_idx (L := X.EL.lay) (orc := X.orc) (fr := X.fr) (n := (X.EL.trec t).count)
    (es := 1) (rfl : ev X.EL.lay X.orc X.fr (.addr (.tab (X.EL.tnr t))) st1 ρC =
      some (.ptr ⟨.tab (X.EL.tnr t), 0⟩, st1)) (ev_cast CIT.u64 h2 ck) ⟨k0, by omega⟩ hpa
  have hl := corr_leseSlot X.EL σ st2 hc2 t hgt (eval σ i σ ρG).n f k0 (by omega)
  rw [hty] at hl
  have hload := ev_ld hidx hl
  have hb := encW_byte hf (σ.slots t (eval σ i σ ρG).n f)
  have r0 := (cast (congrArg (Wert D) hf) (σ.slots t (eval σ i σ ρG).n f) : Zahl 0 255).lo_le
  have r1 := (cast (congrArg (Wert D) hf) (σ.slots t (eval σ i σ ρG).n f) : Zahl 0 255).le_hi
  have i32lo : CIT.i32.lo = -2147483648 := by decide
  have i32hi : CIT.i32.hi = 2147483647 := by decide
  have cb : conv CIT.i32 (encW (D.typ t f) (σ.slots t (eval σ i σ ρG).n f)) =
      some (encW (D.typ t f) (σ.slots t (eval σ i σ ρG).n f)) :=
    conv_id ⟨by rw [hb]; omega, by rw [hb]; omega⟩
  exact ⟨_, st2, ev_condT hcmp htr hload cb, valCorr_encW _ _ _ (X.EL.fnr_fits t f)⟩

end Bytes

/-! ## 6. H8-H10: device registers, through the observation trace -/

/-- H8. The device handle `(volatile uint8_t *)(uintptr_t)BASE` plus the
    register offset `K`: a pointer into the window of device `d`, defined
    only at the declared base (`devHandle`) and inside the window. -/
theorem ev_devReg (L : CLayout) (orc : DevOrc) (fr : Nat) (d : Nat) (B : BlkLay)
    (hL : L (.dev d) = some B) (hk : B.kind = .mmio) (Kr : Nat) (hK : Kr ≤ B.lay.size)
    (st : CSt) (ρ : CLok) :
    ev L orc fr (.padd (.devH d B.base) (.lit Kr)) st ρ = some (.ptr ⟨.dev d, Kr⟩, st) := by
  have hh : devHandle L d B.base = some ⟨.dev d, 0⟩ := by
    unfold devHandle
    rw [hL]
    dsimp only
    rw [if_pos ⟨hk, rfl⟩]
  have hp : ptrAdd L ⟨.dev d, 0⟩ (Kr : Int) 1 = some ⟨.dev d, (Kr : Int)⟩ := by
    have e1 : (⟨.dev d, 0⟩ : CPtr).off + (Kr : Int) * ((1 : Nat) : Int) = (Kr : Int) := by
      show (0 : Int) + _ * ((1 : Nat) : Int) = _
      rw [Int.natCast_one, Int.mul_one, Int.zero_add]
    rw [ptrAdd_progress L _ _ 1 _ hL (by rw [e1]; omega) (by rw [e1]; omega), e1]
  simp only [ev, hh, hp]

/-- Evaluation rule of a volatile load. -/
theorem ev_vld {L : CLayout} {orc : DevOrc} {fr : Nat} {p : CX} {τ : CTy} {st st1 st2 : CSt}
    {ρ : CLok} {q : CPtr} {v : Int} (hp : ev L orc fr p st ρ = some (.ptr q, st1))
    (hl : vLoad L orc st1 q τ = some (v, st2)) :
    ev L orc fr (.vld p τ) st ρ = some (.int v, st2) := by
  simp only [ev, hp, hl]

section Geraet

variable (X : TVCtx D) {Γ : Ctx} {Λ : List (Res D)} (K : CEnvLay D Γ)

/-- H9. `T x = (*(volatile T *)(BASE + K));` against `let x = R;`
    (`regLies`), at a program point where the device window is alive. The
    C device answer and Gabbro's register oracle describe the same device
    (`hdev`, the assumption at the register); the register's type encodes
    the raw answer (`henc`). If the Gabbro read passes its type and
    its device promise (otherwise it is a hardware outcome), the C read
    binds the encoded value, appends exactly one observation and changes
    no memory. -/
theorem regLies_step (r : D.Reg) (d : Nat) (B : BlkLay) (hL : X.EL.lay (.dev d) = some B)
    (hk : B.kind = .mmio) (Kr : Nat) (w : CWidth) (hcell : B.lay.cell Kr = some (.int false w))
    (σ : World D) (st : CSt) (hc : corrW X.EL σ st) (hlive : st.live (.dev d) = true)
    (ρG : Env D Γ) (ρC : CLok) (hr : EnvRel X.EL K ρG ρC) (hK : K.okB = true) {x : Nat}
    (hf : K.freshB x = true) (τc : CTy) (hfit : tyFits (D.rtyp r) τc = true)
    (hdev : cWrap w (X.orc st.obs ⟨.dev d, Kr⟩ (.int false w)) = X.O.regLies r σ)
    (v : Wert D (D.rtyp r)) (hv : einpassen (D.rtyp r) (X.O.regLies r σ) = some v)
    (henc : encW (D.rtyp r) v = X.O.regLies r σ) :
    ∃ st', Exec X.EL.lay X.orc X.fr X.CR X.XR
        (.set x τc (.vld (.padd (.devH d B.base) (.lit Kr)) (.int false w))) st ρC
        (.norm st' (lokUpd ρC x (.int (X.O.regLies r σ)))) ∧
      corrW X.EL σ st' ∧
      st'.obs = .vrd ⟨.dev d, Kr⟩ (.int false w) (X.O.regLies r σ) :: st.obs ∧
      EnvRel X.EL (K.push (D.rtyp r) x) (.cons v ρG) (lokUpd ρC x (.int (X.O.regLies r σ))) ∧
      (∀ {V : Vertrag D} {l : Bool} {Λ' : List (Res D)} (hkl : (D.rklasse r).lesbar = true)
        (rest : Block D V l (D.rtyp r :: Γ) Λ Λ'), D.rzusage r v = true →
        execBlock X.O X.passes X.R (Block.regLies r hkl rest) σ ρG =
          (execBlock X.O X.passes X.R rest σ (.cons v ρG)).schrumpf) := by
  have hin := accOk_inside hL (show accOk X.EL.lay st ⟨.dev d, (Kr : Int)⟩ (.int false w) .vol = true by
    unfold accOk
    rw [show (⟨.dev d, (Kr : Int)⟩ : CPtr).blk = .dev d from rfl, hL]
    dsimp only
    rw [hlive, hk, show ((Kr : Nat) : Int).toNat = Kr from Int.toNat_natCast _, hcell]
    simp [BKind.permits])
  have hacc : accOk X.EL.lay st ⟨.dev d, (Kr : Int)⟩ (.int false w) .vol = true := by
    unfold accOk
    rw [show (⟨.dev d, (Kr : Int)⟩ : CPtr).blk = .dev d from rfl, hL]
    dsimp only
    rw [hlive, hk, show ((Kr : Nat) : Int).toNat = Kr from Int.toNat_natCast _, hcell]
    simp [BKind.permits]
  have hpos := ev_devReg X.EL.lay X.orc X.fr d B hL hk Kr (by
    rw [Int.toNat_natCast] at hin; omega) st ρC
  have hvl : vLoad X.EL.lay X.orc st ⟨.dev d, (Kr : Int)⟩ (.int false w) =
      some (X.O.regLies r σ, CSt.mk st.mem st.live (.vrd ⟨.dev d, Kr⟩ (.int false w)
        (X.O.regLies r σ) :: st.obs)) := by
    unfold vLoad
    rw [if_pos hacc, ← hdev]
  have hev : ev X.EL.lay X.orc X.fr (.vld (.padd (.devH d B.base) (.lit Kr)) (.int false w)) st ρC =
      some (.int (X.O.regLies r σ), CSt.mk st.mem st.live (.vrd ⟨.dev d, Kr⟩ (.int false w)
        (X.O.regLies r σ) :: st.obs)) :=
    ev_vld hpos hvl
  have hvc : ValCorr X.EL (D.rtyp r) v (.int (X.O.regLies r σ)) := by
    rw [← henc]
    exact valCorr_encW _ τc v hfit
  have hconv : convV τc (.int (X.O.regLies r σ)) = some (.int (X.O.regLies r σ)) := by
    rw [← henc]
    exact convV_of_valFits _ _ (encW_fits _ _ v hfit)
  refine ⟨_, Exec.set hev hconv, hc, rfl, envRel_push hK hf hr v _ hvc, ?_⟩
  intro V l Λ' hkl rest hz
  show (match einpassen (D.rtyp r) (X.O.regLies r σ) with
    | Option.some v => if D.rzusage r v then (execBlock X.O X.passes X.R rest σ (.cons v ρG)).schrumpf
        else .hardware (.geraet r)
    | Option.none => .hardware (.register r)) = _
  rw [hv]
  dsimp only
  rw [if_pos hz]

/-- H10. `(*(volatile T *)(BASE + K)) = e;` against `R = e;` (`regSchreib`),
    at a point where the window is alive: exactly one observation carrying
    the written value (Gabbro's `O.regSchreib r (roh v)` receives the same
    number for an integer register), and no memory changes. -/
theorem regSchreib_step {V : Vertrag D} {l : Bool} (r : D.Reg)
    (hkl : (D.rklasse r).schreibbar = true) {e : Expr D Γ Λ (D.rtyp r)} {ce : CX}
    (he : ExprCorr X K ce e) (d : Nat) (B : BlkLay) (hL : X.EL.lay (.dev d) = some B)
    (hk : B.kind = .mmio) (Kr : Nat) (w : CWidth) (hcell : B.lay.cell Kr = some (.int false w))
    (hfit : tyFits (D.rtyp r) (.int false w) = true) (σ : World D) (st : CSt)
    (hc : corrW X.EL σ st) (hlive : st.live (.dev d) = true) (ρG : Env D Γ) (ρC : CLok)
    (hr : EnvRel X.EL K ρG ρC) :
    ∃ st1 st' : CSt, Exec X.EL.lay X.orc X.fr X.CR X.XR
        (.vstore (.padd (.devH d B.base) (.lit Kr)) (.int false w) ce) st ρC (.norm st' ρC) ∧
      StOut X 0 K (execStmt X.O X.passes X.R (Stmt.regSchreib (V := V) (l := l) r hkl e) σ ρG)
        (.norm st' ρC) ∧
      st'.obs = .vwr ⟨.dev d, Kr⟩ (.int false w)
        (encW (D.rtyp r) (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρG)) :: st1.obs := by
  have hc' : corrW X.EL (σ.lese Λ e.orte) st := (corrW_lese _ _ _ _ _).mpr hc
  obtain ⟨v, st1, h1, hv, hc1⟩ := he.run X K hc' hr
  have hve := valCorr_int_of_fits _ _ _ _ hfit hv
  subst hve
  have hs := ev_same _ _ _ _ _ _ _ _ h1
  have hlive1 : st1.live (.dev d) = true := by rw [hs.2]; exact hlive
  have hin : Kr < B.lay.size := by
    have := accOk_inside hL (show accOk X.EL.lay st ⟨.dev d, (Kr : Int)⟩ (.int false w) .vol = true by
      unfold accOk
      rw [show (⟨.dev d, (Kr : Int)⟩ : CPtr).blk = .dev d from rfl, hL]
      dsimp only
      rw [hlive, hk, show ((Kr : Nat) : Int).toNat = Kr from Int.toNat_natCast _, hcell]
      simp [BKind.permits])
    rwa [Int.toNat_natCast] at this
  have hacc : accOk X.EL.lay st1 ⟨.dev d, (Kr : Int)⟩ (.int false w) .vol = true := by
    unfold accOk
    rw [show (⟨.dev d, (Kr : Int)⟩ : CPtr).blk = .dev d from rfl, hL]
    dsimp only
    rw [hlive1, hk, show ((Kr : Nat) : Int).toNat = Kr from Int.toNat_natCast _, hcell]
    simp [BKind.permits]
  have hvf := encW_fits _ _ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρG) hfit
  have hvs : vStore X.EL.lay st1 ⟨.dev d, (Kr : Int)⟩ (.int false w)
      (encW (D.rtyp r) (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρG)) =
      some (CSt.mk st1.mem st1.live (.vwr ⟨.dev d, Kr⟩ (.int false w)
        (encW (D.rtyp r) (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρG)) :: st1.obs)) := by
    unfold vStore
    rw [hacc, hvf]
    rfl
  refine ⟨st1, _, Exec.vstore (ev_devReg X.EL.lay X.orc X.fr d B hL hk Kr (by omega) st ρC) h1
    (convV_of_valFits _ _ hvf) hvs, ⟨_, ρC, rfl, hc1, hr⟩, rfl⟩

end Geraet

/-
CUTS: what this pass does not do, by name.
- DEVICE WINDOWS ARE NOT IN THE RELATION. `corrW` relates memory; a
  device window is no memory, so its liveness is not an invariant the
  pass-(i) judgements carry, and the register forms (H9, H10) are per-step
  lemmas with the window's liveness as a premise. Carrying device
  liveness through `StmtCorr` would put it into every judgement.
- THE DEVICE ANSWER is related by assumption (`hdev`): the C device oracle
  and Gabbro's `Orakel.regLies` describe the same device. Gabbro's
  `regSchreib` has no record (`Unit`), so the written value is related to
  C's observation only by the lemma's conclusion, not to a Gabbro trace.
  `transition` (read-modify-write with the mirror), the bank accessors
  and port I/O (`inb`/`outb` helpers, `portIn`/`portOut`) are not covered.
- THE BYTE VIEW's pointer `v->bytes` is related at a program point
  (`le32_corr_at`) or through `PtrTo`; how the view got its pointer (the
  driver's buffer, a foreign object) is not modelled. The big-endian and
  64-bit readers, the writers `gabbro_setz_*` and the format bit-field
  accessors have the same shape and are not covered; `schreibBytes` is
  not covered.
- `exchange update` (the CAS loop, 9016ff.) is not given its loop lemma:
  only its compare-exchange step (success and failure) is. The weak form
  may fail spuriously; the model's `aCas` is strong (CSpeicher's CUT).
- TAGGED UNIONS are not covered: the memory model has no union cells
  (CSpeicher's CUT), and the emitter has no lowering for a variant
  constructor -- `V(x)` falls to the generic call text `V(x)` (12632), a
  call of a function nobody declares (survey finding, not re-measured).
  `onTag`'s `switch (m.marke)` has `CS.sw`'s semantics and no lemma.
- THE FOREIGN STEP (`AxCorr`) is an assumption per foreign function; the
  `bindAxiom` form (a foreign call with an answer) is not covered.
- `goto` is covered in its two emitted jump targets; the `exchange update`
  body's `goto _cnN_fertig` is not.
-/

#print axioms scorr_leave
#print axioms scorr_next
#print axioms scorr_publish
#print axioms bsem_awaits
#print axioms cas_success
#print axioms cas_failure
#print axioms scorr_axiomCall
#print axioms lor_bytes
#print axioms ev_le32
#print axioms le32_corr_at
#print axioms ecorr_le32
#print axioms ecorr_byteGuard
#print axioms ev_devReg
#print axioms regLies_step
#print axioms regSchreib_step

end Gabbro.Grammatik
