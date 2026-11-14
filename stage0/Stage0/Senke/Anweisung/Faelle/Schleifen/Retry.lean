/- The actual retry lowering uses one reserved counter and one body image. -/
module
public import Stage0.Senke.Anweisung.Faelle.Schleifen.Retrying.Execution
public import Stage0.Senke.Anweisung.Faelle.Kontext
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}
variable {H sc : List D.Lock} {reserved : Nat}

theorem retry_case {O : Orakel D} {passes : Nat}
    {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : W} {cap : Nat}
    {P : Programm D} {f : D.Fn} {fp : W} {K Ks lo : Nat} {rp cfp : W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = (functionFrame P f).internalResult) {pr : List Nat} {ex : Int × Int}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {n : Nat} {bis : Expr D Γ Λ .bool}
    {body : Block D (vertragVon D f) true Γ Λ Λ} {overflow : Block D (vertragVon D f) l Γ Λ Λ}
    (ihBody : ∀ {pr ex}, BlockCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex H sc body reserved)
    (ihOverflow : ∀ {pr ex}, BlockCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex H sc overflow reserved) :
    StmtCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex H sc (.retry n bis body overflow) reserved := by
  intro c top h hK hs hW m pc σ ρ hp hlo hlo2 hu hk hw hpr
  dsimp only [lowS, ← hlo0, resultWords_vertragVon] at h
  split at h
  · rename_i allowed
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨cc, hcc, cu, hcu, emitted⟩ := h
    obtain ⟨cb, tb, hcb, rfl, htc, htb, htu, hcounter, hone, hscratch, fuel, imageSize⟩ :=
      retryC_actual emitted
    let counter := (counterPair reserved (counterDepthB body)).1
    let one := (counterPair reserved (counterDepthB body)).2
    have pairStep : counter + 1 = one := rfl
    have controlBounds : lo ≤ counter ∧ counter < one ∧ one < FB + reserved := by
      dsimp only [counter, one]
      exact ⟨by rw [hlo0]; exact allowed.1, by omega, allowed.2.1⟩
    have room : frei Γ reserved ≤ K := by have := hW.ks; omega
    have protectedSlots : ∀ j ∈ pr, j < frei Γ reserved ∧ j ≠ counter ∧ j ≠ one := by
      intro j hj
      refine ⟨hpr j hj, ?_, ?_⟩
      · intro eq
        apply allowed.2.2.1
        change counter ∈ pr
        rw [← eq]
        exact hj
      · intro eq
        apply allowed.2.2.2
        change one ∈ pr
        rw [← eq]
        exact hj
    obtain ⟨m1, initRun, initFrame, entry, surrounds, snapshot, world, keeps, count, unit⟩ :=
      forever_initialize_entry (lo := lo) (pr := pr) hW hp hu hk hw
        (by rw [hlo0]) controlBounds.1 (by omega) (by omega) controlBounds.2.2
        (by omega) room fuel (by
          intro j hj
          have member := protectedSlots j hj
          exact ⟨by omega, member.2⟩)
    let x : Retrying.Image L P f Γ reserved :=
      { A := A
        C := C
        dv := dv
        fp := fp
        pc := pc + 32
        rp := rp
        cfp := cfp
        K := K
        Ks := Ks
        lo := lo
        counter := counter
        one := one
        condition := cc.1
        body := cb
        overflow := cu.1
        σ0 := σ0
        ρ0 := ρ0
        pr := pr
        H := H
        layout := hW
        abi := hlo0
        low := hlo
        controls := controlBounds
        room := (by omega)
        kept := protectedSlots
        sized := imageSize }
    have ready : x.Ready m1 σ ρ :=
      { pre := entry
        surround := surrounds
        head := snapshot
        world := world }
    have exitAt : x.addr x.exitIndex = pc + BitVec.ofNat 64
        (16 * (retryCode counter one (frei Γ reserved) n cc.1 cb cu.1).length) := by
      change pc + BitVec.ofNat 64 (16 * 2) + _ = _
      rw [addr_norm, retryCode_length]
      apply congrArg (fun k : Nat => pc + BitVec.ofNat 64 k)
      dsimp only [Retrying.Image.exitIndex, x]
      omega
    have bodyBack : x.addr x.bodyIndex + BitVec.ofNat 64 (16 * cb.length) = x.addr x.backIndex :=
      step_eq x.pc (by dsimp only [Retrying.Image.bodyIndex, Retrying.Image.backIndex, x]; omega)
    have bodyLeave : x.addr x.backIndex +
        BitVec.ofInt 64 (retryTargets cc.1.length cb.length cu.1.length).1 = x.addr x.exitIndex :=
      adr_eq x.pc (x := x.backIndex) (y := x.exitIndex) (by
        dsimp only [retryTargets, Retrying.Image.backIndex, Retrying.Image.exitIndex, x]; omega)
    have bodyNext : x.addr x.backIndex +
        BitVec.ofInt 64 (retryTargets cc.1.length cb.length cu.1.length).2 = x.pc := by
      have h := adr_eq (pc := x.pc) (x := x.backIndex) (y := 0)
        (J := (retryTargets cc.1.length cb.length cu.1.length).2)
        (by dsimp only [retryTargets, Retrying.Image.backIndex, x]; omega)
      exact h.trans (BitVec.add_zero x.pc)
    have overflowEnd : x.addr x.overflowIndex + BitVec.ofNat 64 (16 * cu.1.length) = x.addr x.exitIndex :=
      step_eq x.pc (by dsimp only [Retrying.Image.overflowIndex, Retrying.Image.exitIndex, x]; omega)
    have simulation := x.correct (bis := bis) (tc := cc.2) (sc := sc) hcc
      (by change cc.2 ≤ Ks; omega) (execBlock O passes R body)
      (execBlock O passes R overflow)
      (outerLeave := x.addr x.exitIndex + BitVec.ofInt 64 ex.1)
      (outerNext := x.addr x.exitIndex + BitVec.ofInt 64 ex.2)
      (bodyRun := by
        intro mem σ' ρ' ready'
        have run := ihBody (pr := counter :: one :: pr)
          (ex := retryTargets cc.1.length cb.length cu.1.length) cb tb hcb
          (by omega) (by omega) hW mem (x.addr x.bodyIndex) σ' ρ' ready'.body
          hlo hlo2 ready'.surround ready'.head ready'.world (by
            intro j hj
            rcases List.mem_cons.mp hj with rfl | hj
            · unfold frei; omega
            · rcases List.mem_cons.mp hj with rfl | hj
              · unfold frei; omega
              · exact hpr j hj)
        rw [bodyBack, bodyLeave, bodyNext] at run
        exact run)
      (overflowRun := by
        intro mem σ' ρ' ready'
        have run := ihOverflow cu.1 cu.2 hcu (by omega) (by omega) hW mem
          (x.addr x.overflowIndex) σ' ρ' ready'.overflow hlo hlo2
          ready'.surround ready'.head ready'.world hpr
        rw [overflowEnd] at run
        exact run)
      n m1 σ ρ ⟨ready, count, unit, by omega⟩
    rw [exitAt] at simulation
    exact Sim.prefix hlo initRun.forget initFrame keeps simulation
  · cases h

/-- Fuel zero stops before even reading the invariant. -/
theorem forever_zero {V : Vertrag D} {Γ : Ctx} {Λ : List (Res D)} {l : Bool}
    (a : D.Annahme) (inv : Expr D Γ Λ .bool) (body : Block D V true Γ Λ Λ)
    (O : Orakel D) (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f)
    (σ : World D) (ρ : Env D Γ) :
    execStmt O 0 R (show Stmt D V l Γ Λ Λ from .forever a inv body) σ ρ = .hardware (.fortschritt a) := by rfl

/-- One pass checks a false invariant, whereas zero passes answers the progress assumption. -/
theorem forever_one_false {V : Vertrag D} {Γ : Ctx} {Λ : List (Res D)} {l : Bool}
    (a : D.Annahme) (body : Block D V true Γ Λ Λ)
    (O : Orakel D) (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f)
    (σ : World D) (ρ : Env D Γ) :
    execStmt O 1 R (show Stmt D V l Γ Λ Λ from .forever a .fls body) σ ρ = .logik .schleife := by rfl

end Gabbro.Stage0.Senke
