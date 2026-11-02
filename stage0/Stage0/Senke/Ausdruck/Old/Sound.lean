/- Postconditions reuse the ordinary full-value expression kernels.
   The combined environment keeps all captured entry values available in every recursive premise. -/
module
public import Stage0.Senke.Ausdruck.Old.Basic
public import Stage0.Senke.Ausdruck.Aggregat.Frame.Copy
@[expose] public section


namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
set_option linter.unusedSectionVars false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
variable [Kern] {D : Deklaration} {L : Lay D}

/-- A saved complete span is read through the common full-value copy theorem. -/
theorem snapshot_copy {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {τ : Ty} {v : Wert D τ} {m : Runner.Mem} {pc fp : Runner.W} {K d src reserved : Nat}
    (pre : Pre L m pc fp K d (copyWords (valueWords τ) d src) ρ W reserved)
    (value : ValueAt L m fp src τ v) (before : src + valueWords τ ≤ d)
    (fits : d + valueWords τ ≤ K) :
    ValueOk L m pc fp K d (copyWords (valueWords τ) d src) τ v := by
  obtain ⟨m', run, changed, output⟩ := copyValue_run pre.frame pre.small
    fits (by omega) (Or.inr before) pre.code (by simpa only [copyWords_length] using pre.far) value
  exact ⟨m', by simpa only [copyWords_length] using run, Agree.widen changed fits, output⟩

theorem lowEnsAt_ok (layout : FrameLayout) (start : Nat)
    {Λ : List (Res D)} {fp : Runner.W} {K : Nat} {W : Runner.Mem → Prop}
    (σ0 σ : World D) (hWL : ∀ m, W m → WeltAt m L σ) (hLay : LayIn L)
    {Φ Γ : Ctx} (full : Env D Φ) (ρ : Env D Γ)
    (paramsOfFull : ∀ {m}, EnvAt L m fp full → EnvAt L m fp ρ layout.ensReserved)
    (context : frei Γ layout.ensReserved ≤ frei Φ) :
    {τ : Ty} → (e : Expr D Γ Λ τ) → (d : Nat) → (code : List II) → (top : Nat) →
    lowEnsAt L layout start e d = some (code, top) → top ≤ K →
    (∀ {m}, EnvAt L m fp full → EntrySnapshots.At L σ0 m fp (oldCells e) start) →
    start + EntrySnapshots.words (oldCells e) ≤ frei Φ →
    ∀ (m : Runner.Mem) (pc : Runner.W), Pre L m pc fp K d code full W →
      ValueOk L m pc fp K d code τ (eval σ0 e σ ρ)
  | _, .oldG g _, d, code, top, lower, fits, saved, before, m, pc, pre => by
    obtain ⟨rfl, rfl⟩ := Option.some.inj lower
    have value := (saved pre.env).1
    have ctx := pre.ctx
    exact snapshot_copy pre value
      (by simp only [oldCells, EntrySnapshots.words, Nat.add_zero, Zelle.ty] at before; omega) fits
  | _, .oldS t f i _, d, code, top, lower, fits, saved, before, m, pc, pre => by
    cases index : entryIndex i with
    | some k =>
      simp only [lowEnsAt, index, Option.some.injEq, Prod.mk.injEq] at lower
      obtain ⟨rfl, rfl⟩ := lower
      have value : ValueAt L m fp start (D.typ t f) (σ0.slots t k.toNat f) := by
        have stored := saved pre.env
        simpa only [oldCells, index, EntrySnapshots.At, Zelle.ty, Zelle.val, and_true] using stored
      have equal := entryIndex_ok σ0 σ ρ i index
      simp only [intValue, Option.some.injEq] at equal
      have nonnegative : 0 ≤ k := by
        have bound := (eval σ0 i σ ρ).lo_le
        change 0 ≤ _ at bound
        omega
      have ctx := pre.ctx
      have run := snapshot_copy pre value
        (by simp only [oldCells, index, EntrySnapshots.words, Nat.add_zero, Zelle.ty] at before; omega) fits
      simpa only [eval, equal, Int.toNat_of_nonneg nonnegative] using run
    | none =>
      simp only [lowEnsAt, index] at lower
      split at lower
      · next available =>
        have captures {m} (env : EnvAt L m fp full) :
            EntrySnapshots.At L σ0 m fp
              (oldCells i ++ EntrySnapshots.column t f 0 (D.count t).toNat) start := by
          simpa only [oldCells, index, available, ite_true] using saved env
        have bound : start + EntrySnapshots.words (oldCells i) +
            (D.count t).toNat * valueWords (D.typ t f) ≤ frei Φ := by
          simpa only [oldCells, index, available, ite_true, EntrySnapshots.words_append,
            EntrySnapshots.column_words, Nat.add_assoc] using before
        have literal := (of_decide_eq_true available).2.1
        apply entryColumnL_ok (eval σ0 i σ ρ) (σ0.slots t (eval σ0 i σ ρ).n f)
          bound literal ?_ ?_ lower fits m pc pre
        · intro m env
          have valid := eval σ0 i σ ρ
          have range : valid.n.toNat < (D.count t).toNat := by
            have := valid.lo_le
            have := valid.le_hi
            omega
          have value := EntrySnapshots.column_at t f (D.count t).toNat 0
            (start + EntrySnapshots.words (oldCells i)) valid.n.toNat range (captures env).right
          simpa only [Nat.zero_add, Int.toNat_of_nonneg valid.lo_le] using value
        · intro ci ti emitted childFits m pc childPre
          exact lowEnsAt_ok layout start σ0 σ hWL hLay full ρ paramsOfFull context
            i _ ci ti emitted childFits (fun env => (captures env).left) (by omega) m pc childPre
      · cases lower
  | _, .widen lower upper e, d, code, top, emitted, fits, saved, before, m, pc, pre =>
    resizeIntegerL_ok (eval σ0 e σ ρ) (Zahl.weiter lower upper (eval σ0 e σ ρ)) rfl
      (fun cc tt hc ht hp => lowEnsAt_ok layout start σ0 σ hWL hLay full ρ paramsOfFull context
        e d cc tt hc ht saved before m pc hp) emitted fits pre
  | _, .add a b, d, code, top, lower, fits, saved, before, m, pc, pre => by
    apply wideAdd_ok (eval σ0 a σ ρ) (eval σ0 b σ ρ)
      (fa := lowEnsAt L layout start a)
      (fb := lowEnsAt L layout (start + EntrySnapshots.words (oldCells a)) b)
      (fun cc tt hc ht m pc hp => lowEnsAt_ok layout start σ0 σ hWL hLay full ρ paramsOfFull context
        a _ cc tt hc ht (fun env => (saved env).left)
        (by simp only [oldCells, EntrySnapshots.words_append] at before; omega) m pc hp)
      (fun cc tt hc ht m pc hp => lowEnsAt_ok layout (start + EntrySnapshots.words (oldCells a))
        σ0 σ hWL hLay full ρ paramsOfFull context b _ cc tt hc ht (fun env => (saved env).right)
        (by simp only [oldCells, EntrySnapshots.words_append] at before; omega) m pc hp)
      lower fits pre
  | _, .sub a b, d, code, top, lower, fits, saved, before, m, pc, pre => by
    apply wideSub_ok (eval σ0 a σ ρ) (eval σ0 b σ ρ)
      (fa := lowEnsAt L layout start a)
      (fb := lowEnsAt L layout (start + EntrySnapshots.words (oldCells a)) b)
      (fun cc tt hc ht m pc hp => lowEnsAt_ok layout start σ0 σ hWL hLay full ρ paramsOfFull context
        a _ cc tt hc ht (fun env => (saved env).left)
        (by simp only [oldCells, EntrySnapshots.words_append] at before; omega) m pc hp)
      (fun cc tt hc ht m pc hp => lowEnsAt_ok layout (start + EntrySnapshots.words (oldCells a))
        σ0 σ hWL hLay full ρ paramsOfFull context b _ cc tt hc ht (fun env => (saved env).right)
        (by simp only [oldCells, EntrySnapshots.words_append] at before; omega) m pc hp)
      lower fits pre
  | _, .mul a b, d, code, top, lower, fits, saved, before, m, pc, pre => by
    apply wideMul_ok (eval σ0 a σ ρ) (eval σ0 b σ ρ)
      (fa := lowEnsAt L layout start a)
      (fb := lowEnsAt L layout (start + EntrySnapshots.words (oldCells a)) b)
      (fun cc tt hc ht m pc hp => lowEnsAt_ok layout start σ0 σ hWL hLay full ρ paramsOfFull context
        a _ cc tt hc ht (fun env => (saved env).left)
        (by simp only [oldCells, EntrySnapshots.words_append] at before; omega) m pc hp)
      (fun cc tt hc ht m pc hp => lowEnsAt_ok layout (start + EntrySnapshots.words (oldCells a))
        σ0 σ hWL hLay full ρ paramsOfFull context b _ cc tt hc ht (fun env => (saved env).right)
        (by simp only [oldCells, EntrySnapshots.words_append] at before; omega) m pc hp)
      lower fits pre
  | _, .eq a b, d, code, top, lower, fits, saved, before, m, pc, pre => by
    apply wideEq_ok (eval σ0 a σ ρ) (eval σ0 b σ ρ)
      (fa := lowEnsAt L layout start a)
      (fb := lowEnsAt L layout (start + EntrySnapshots.words (oldCells a)) b)
      (fun cc tt hc ht m pc hp => lowEnsAt_ok layout start σ0 σ hWL hLay full ρ paramsOfFull context
        a _ cc tt hc ht (fun env => (saved env).left)
        (by simp only [oldCells, EntrySnapshots.words_append] at before; omega) m pc hp)
      (fun cc tt hc ht m pc hp => lowEnsAt_ok layout (start + EntrySnapshots.words (oldCells a))
        σ0 σ hWL hLay full ρ paramsOfFull context b _ cc tt hc ht (fun env => (saved env).right)
        (by simp only [oldCells, EntrySnapshots.words_append] at before; omega) m pc hp)
      lower fits pre
  | _, .lt a b, d, code, top, lower, fits, saved, before, m, pc, pre => by
    apply wideLt_ok (eval σ0 a σ ρ) (eval σ0 b σ ρ)
      (fa := lowEnsAt L layout start a)
      (fb := lowEnsAt L layout (start + EntrySnapshots.words (oldCells a)) b)
      (fun cc tt hc ht m pc hp => lowEnsAt_ok layout start σ0 σ hWL hLay full ρ paramsOfFull context
        a _ cc tt hc ht (fun env => (saved env).left)
        (by simp only [oldCells, EntrySnapshots.words_append] at before; omega) m pc hp)
      (fun cc tt hc ht m pc hp => lowEnsAt_ok layout (start + EntrySnapshots.words (oldCells a))
        σ0 σ hWL hLay full ρ paramsOfFull context b _ cc tt hc ht (fun env => (saved env).right)
        (by simp only [oldCells, EntrySnapshots.words_append] at before; omega) m pc hp)
      lower fits pre
  | _, .le a b, d, code, top, lower, fits, saved, before, m, pc, pre => by
    apply wideLe_ok (eval σ0 a σ ρ) (eval σ0 b σ ρ)
      (fa := lowEnsAt L layout start a)
      (fb := lowEnsAt L layout (start + EntrySnapshots.words (oldCells a)) b)
      (fun cc tt hc ht m pc hp => lowEnsAt_ok layout start σ0 σ hWL hLay full ρ paramsOfFull context
        a _ cc tt hc ht (fun env => (saved env).left)
        (by simp only [oldCells, EntrySnapshots.words_append] at before; omega) m pc hp)
      (fun cc tt hc ht m pc hp => lowEnsAt_ok layout (start + EntrySnapshots.words (oldCells a))
        σ0 σ hWL hLay full ρ paramsOfFull context b _ cc tt hc ht (fun env => (saved env).right)
        (by simp only [oldCells, EntrySnapshots.words_append] at before; omega) m pc hp)
      lower fits pre
  | _, .neg a, d, code, top, lower, fits, saved, before, m, pc, pre =>
    wideNeg_ok (eval σ0 a σ ρ)
      (fa := lowEnsAt L layout start a)
      (fun cc tt hc ht m pc hp => lowEnsAt_ok layout start σ0 σ hWL hLay full ρ paramsOfFull context
        a _ cc tt hc ht saved before m pc hp) lower fits pre
  | _, .not a, d, code, top, lower, fits, saved, before, m, pc, pre => by
    simp only [lowEnsAt, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at lower
    obtain ⟨⟨ca, ta⟩, ha, out⟩ := lower
    simp only [bin2, Prod.mk.injEq] at out
    obtain ⟨rfl, rfl⟩ := out
    refine Ok.value (width := rfl) ?_
    refine bin_ok
      (fun m pc hp => (lowEnsAt_ok layout start σ0 σ hWL hLay full ρ paramsOfFull context
        a d ca ta ha (by omega) saved before m pc hp).word trivial)
      (fun m pc hp => const_ok hp (by decide) (by omega))
      (g := fun x y => some (x ^^^ y)) ?_ rfl (by decide) (by omega) pre
    intro wa wb pa pb
    refine ⟨_, rfl, ?_⟩
    simp only [Enc, eval] at pa ⊢
    rw [pa, pb]
    simp only [wahr?]
    exact not_word _
  | _, .and a b, d, code, top, lower, fits, saved, before, m, pc, pre => by
    simp only [lowEnsAt, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at lower
    obtain ⟨⟨ca, ta⟩, ha, ⟨cb, tb⟩, hb, out⟩ := lower
    simp only [bin2, Prod.mk.injEq] at out
    obtain ⟨rfl, rfl⟩ := out
    have bound := lowEnsAt_top layout (start + EntrySnapshots.words (oldCells a)) b (d + 1) cb tb hb
    refine Ok.value (width := rfl) ?_
    refine bin_ok
      (fun m pc hp => (lowEnsAt_ok layout start σ0 σ hWL hLay full ρ paramsOfFull context
        a d ca ta ha (by omega) (fun env => (saved env).left)
        (by simp only [oldCells, EntrySnapshots.words_append] at before; omega) m pc hp).word trivial)
      (fun m pc hp => (lowEnsAt_ok layout (start + EntrySnapshots.words (oldCells a))
        σ0 σ hWL hLay full ρ paramsOfFull context b (d + 1) cb tb hb (by omega)
        (fun env => (saved env).right)
        (by simp only [oldCells, EntrySnapshots.words_append] at before; omega) m pc hp).word trivial)
      (g := fun x y => some (x &&& y)) ?_ rfl (by decide) (by omega) pre
    intro wa wb pa pb
    refine ⟨_, rfl, ?_⟩
    simp only [Enc, eval] at pa pb ⊢
    rw [pa, pb]
    simp only [wahr?]
    exact and_word _ _
  | _, .or a b, d, code, top, lower, fits, saved, before, m, pc, pre => by
    simp only [lowEnsAt, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at lower
    obtain ⟨⟨ca, ta⟩, ha, ⟨cb, tb⟩, hb, out⟩ := lower
    simp only [bin2, Prod.mk.injEq] at out
    obtain ⟨rfl, rfl⟩ := out
    have bound := lowEnsAt_top layout (start + EntrySnapshots.words (oldCells a)) b (d + 1) cb tb hb
    refine Ok.value (width := rfl) ?_
    refine bin_ok
      (fun m pc hp => (lowEnsAt_ok layout start σ0 σ hWL hLay full ρ paramsOfFull context
        a d ca ta ha (by omega) (fun env => (saved env).left)
        (by simp only [oldCells, EntrySnapshots.words_append] at before; omega) m pc hp).word trivial)
      (fun m pc hp => (lowEnsAt_ok layout (start + EntrySnapshots.words (oldCells a))
        σ0 σ hWL hLay full ρ paramsOfFull context b (d + 1) cb tb hb (by omega)
        (fun env => (saved env).right)
        (by simp only [oldCells, EntrySnapshots.words_append] at before; omega) m pc hp).word trivial)
      (g := fun x y => some (x ||| y)) ?_ rfl (by decide) (by omega) pre
    intro wa wb pa pb
    refine ⟨_, rfl, ?_⟩
    simp only [Enc, eval] at pa pb ⊢
    rw [pa, pb]
    simp only [wahr?]
    exact or_word _ _
  | _, .intBuiltin1 op a, d, code, top, lower, fits, saved, before, m, pc, pre =>
    BitBuiltin.unary_ok op (eval σ0 a σ ρ)
      (fun q cc tt hc ht m pc hp => lowEnsAt_ok layout start σ0 σ hWL hLay full ρ paramsOfFull context
        a q cc tt hc ht saved before m pc hp) d code top lower fits m pc pre
  | _, .intBuiltin2 op a b, d, code, top, lower, fits, saved, before, m, pc, pre =>
    intBuiltin2L_ok op (eval σ0 a σ ρ) (eval σ0 b σ ρ)
      (fa := lowEnsAt L layout start a)
      (fb := lowEnsAt L layout (start + EntrySnapshots.words (oldCells a)) b)
      (fun q cc tt hc ht m pc hp => lowEnsAt_ok layout start σ0 σ hWL hLay full ρ paramsOfFull context
        a q cc tt hc ht (fun env => (saved env).left)
        (by simp only [oldCells, EntrySnapshots.words_append] at before; omega) m pc hp)
      (fun q cc tt hc ht m pc hp => lowEnsAt_ok layout (start + EntrySnapshots.words (oldCells a))
        σ0 σ hWL hLay full ρ paramsOfFull context b q cc tt hc ht (fun env => (saved env).right)
        (by simp only [oldCells, EntrySnapshots.words_append] at before; omega) m pc hp)
      lower fits pre
  | _, e@(.lit ..), d, code, top, lower, fits, saved, before, m, pc, pre
  | _, e@(.tru ..), d, code, top, lower, fits, saved, before, m, pc, pre
  | _, e@(.fls ..), d, code, top, lower, fits, saved, before, m, pc, pre
  | _, e@(.var ..), d, code, top, lower, fits, saved, before, m, pc, pre
  | _, e@(.glob ..), d, code, top, lower, fits, saved, before, m, pc, pre
  | _, e@(.slot ..), d, code, top, lower, fits, saved, before, m, pc, pre
  | _, e@(.thru ..), d, code, top, lower, fits, saved, before, m, pc, pre
  | _, e@(.ptrOf ..), d, code, top, lower, fits, saved, before, m, pc, pre
  | _, e@(.fnref ..), d, code, top, lower, fits, saved, before, m, pc, pre
  | _, e@(.div ..), d, code, top, lower, fits, saved, before, m, pc, pre
  | _, e@(.rem ..), d, code, top, lower, fits, saved, before, m, pc, pre
  | _, e@(.sdiv ..), d, code, top, lower, fits, saved, before, m, pc, pre
  | _, e@(.srem ..), d, code, top, lower, fits, saved, before, m, pc, pre
  | _, e@(.getBytes ..), d, code, top, lower, fits, saved, before, m, pc, pre
  | _, e@(.band ..), d, code, top, lower, fits, saved, before, m, pc, pre
  | _, e@(.bor ..), d, code, top, lower, fits, saved, before, m, pc, pre
  | _, e@(.bxor ..), d, code, top, lower, fits, saved, before, m, pc, pre
  | _, e@(.shl ..), d, code, top, lower, fits, saved, before, m, pc, pre
  | _, e@(.shr ..), d, code, top, lower, fits, saved, before, m, pc, pre
  | _, e@(.fllt ..), d, code, top, lower, fits, saved, before, m, pc, pre
  | _, e@(.flle ..), d, code, top, lower, fits, saved, before, m, pc, pre
  | _, e@(.none ..), d, code, top, lower, fits, saved, before, m, pc, pre
  | _, e@(.some ..), d, code, top, lower, fits, saved, before, m, pc, pre
  | _, e@(.istSome ..), d, code, top, lower, fits, saved, before, m, pc, pre
  | _, e@(.case ..), d, code, top, lower, fits, saved, before, m, pc, pre
  | _, e@(.why ..), d, code, top, lower, fits, saved, before, m, pc, pre
  | _, e@(.forallSlots ..), d, code, top, lower, fits, saved, before, m, pc, pre
  | _, e@(.existsSlots ..), d, code, top, lower, fits, saved, before, m, pc, pre
  | _, e@(.reaches ..), d, code, top, lower, fits, saved, before, m, pc, pre
  | _, e@(.refEq ..), d, code, top, lower, fits, saved, before, m, pc, pre
  | _, e@(.slotRef ..), d, code, top, lower, fits, saved, before, m, pc, pre
  | _, e@(.arrNil ..), d, code, top, lower, fits, saved, before, m, pc, pre
  | _, e@(.arrCons ..), d, code, top, lower, fits, saved, before, m, pc, pre
  | _, e@(.arrGet ..), d, code, top, lower, fits, saved, before, m, pc, pre
  | _, e@(.arrSet ..), d, code, top, lower, fits, saved, before, m, pc, pre
  | _, e@(.strLit ..), d, code, top, lower, fits, saved, before, m, pc, pre
  | _, e@(.strLen ..), d, code, top, lower, fits, saved, before, m, pc, pre
  | _, e@(.strCat ..), d, code, top, lower, fits, saved, before, m, pc, pre
  | _, e@(.strGet ..), d, code, top, lower, fits, saved, before, m, pc, pre
  | _, e@(.strEq ..), d, code, top, lower, fits, saved, before, m, pc, pre
  | _, e@(.strLt ..), d, code, top, lower, fits, saved, before, m, pc, pre
  | _, e@(.strWeit ..), d, code, top, lower, fits, saved, before, m, pc, pre
  | _, e@(.wenn ..), d, code, top, lower, fits, saved, before, m, pc, pre
  | _, e@(.count ..), d, code, top, lower, fits, saved, before, m, pc, pre
  | _, e@(.prod ..), d, code, top, lower, fits, saved, before, m, pc, pre
  | _, e@(.prodGet ..), d, code, top, lower, fits, saved, before, m, pc, pre
  | _, e@(.prodSet ..), d, code, top, lower, fits, saved, before, m, pc, pre
  | _, e@(.eng ..), d, code, top, lower, fits, saved, before, m, pc, pre => by
    subst e
    exact lowE_ok (reserved := layout.ensReserved) σ0 σ hWL hLay _ d code top lower fits m pc ρ
      ⟨context.trans pre.ctx, pre.small, pre.frame, pre.code, pre.far,
        paramsOfFull pre.env, pre.welt, pre.wstab⟩

/-- This is the postcondition contract consumed by the actual return proof. -/
theorem lowEns_ok (layout : FrameLayout) {Λ : List (Res D)} {fp : Runner.W}
    {K : Nat} {W : Runner.Mem → Prop}
    (σ0 σ : World D) (hWL : ∀ m, W m → WeltAt m L σ) (hLay : LayIn L)
    {Γ : Ctx} {τ : Ty} (e : Expr D Γ Λ τ) (d : Nat) (code : List II) (top : Nat)
    (lower : lowEns L layout e d = some (code, top)) (fits : top ≤ K)
    (m : Runner.Mem) (pc : Runner.W) (ρ : Env D Γ)
    (pre : Pre L m pc fp K d code ρ W layout.ensReserved)
    (saved : EntrySnapshots.At L σ0 m fp (oldCells e) layout.snapshotBase)
    (complete : layout.snapshotWords = EntrySnapshots.words (oldCells e)) :
    ValueOk L m pc fp K d code τ (eval σ0 e σ ρ) := by
  let cells := oldCells e
  let full := EntrySnapshots.appendEnv ρ (EntrySnapshots.values σ0 cells)
  have environment : EnvAt L m fp full := by
    apply (EntrySnapshots.complete_at ρ σ0 cells).mpr
    constructor
    · simpa only [FrameLayout.ensReserved, complete] using pre.env
    · exact saved
  have paramsOfFull {m} (env : EnvAt L m fp full) : EnvAt L m fp ρ layout.ensReserved := by
    have h := ((EntrySnapshots.complete_at ρ σ0 cells).mp env).1
    simpa only [FrameLayout.ensReserved, complete] using h
  have captures {m} (env : EnvAt L m fp full) :
      EntrySnapshots.At L σ0 m fp (oldCells e) layout.snapshotBase :=
    ((EntrySnapshots.complete_at ρ σ0 cells).mp env).2
  have size : frei Γ layout.ensReserved = frei (Γ ++ EntrySnapshots.types cells) := by
    simp only [frei, EntrySnapshots.contextWords_append, EntrySnapshots.types_words,
      FrameLayout.ensReserved, complete, cells]
    omega
  apply lowEnsAt_ok layout layout.snapshotBase σ0 σ hWL hLay full ρ
    paramsOfFull (Nat.le_of_eq size) e d code top lower fits captures
    (by simp only [FrameLayout.snapshotBase, frei, EntrySnapshots.contextWords_append,
          EntrySnapshots.types_words, cells]; omega) m pc
  exact ⟨by rw [← size]; exact pre.ctx, pre.small, pre.frame, pre.code, pre.far,
    environment, pre.welt, pre.wstab⟩

end Gabbro.Stage0.Senke
