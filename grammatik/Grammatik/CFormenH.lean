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

end Gabbro.Grammatik
