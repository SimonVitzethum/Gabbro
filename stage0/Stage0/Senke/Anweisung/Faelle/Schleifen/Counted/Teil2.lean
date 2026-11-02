module
public import Stage0.Senke.Anweisung.Faelle.Schleifen.Counted.Teil2a

public import Stage0.Senke.Anweisung.Simulation
public import Stage0.Senke.Ausdruck.Gleichungen
public import Stage0.Senke.Anweisung.Faelle.Schleifen.Counted.Teil1

@[expose] public section

namespace Gabbro.Stage0.Senke
open Runner Runner.IR
variable [Kern]
open Gabbro.Grammatik Runner.Mem
variable {D : Deklaration} {L : Lay D} {reserved : Nat}

/-- Actual `lowB .cons` composition for normal outcomes. The second child is
    proved at the memory produced by the first, with code and frame restored
    from its agreement proof. Counts include all executed callee instructions;
    neither child count is replaced by its static code length. -/
theorem countedBlockCons_case
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λmid Λ' : List (Res D)}
    {s : Stmt D V l Γ Λ Λmid} {rest : Block D V l Γ Λmid Λ'}
    {passes lo K Ks ns nr top : Nat} {A : D.Fn → Nat}
    {ens : List II × Nat} {pr : List Nat} {ex : Int × Int}
    {code : List II} {m : Runner.Mem} {pc fp : Runner.W}
    {ρ ρ1 ρ2 : Env D Γ} {σ1 σ2 : World D}
    (lower : lowB (reserved := reserved) passes A L (functionFrame P f) ens pr ex (.cons s rest) =
      some (code, top))
    (inside : WIn L fp Ks K)
    (pre : PreS L m pc fp K (frei Γ reserved) code ρ reserved)
    (stmtRuns : ∀ cr tr cs ts,
      lowB (reserved := reserved) passes A L (functionFrame P f) ens pr ex rest = some (cr, tr) →
      lowS (reserved := reserved) passes A L (functionFrame P f) ens pr (exPlus ex cr.length) s = some (cs, ts) →
      PreS L m pc fp K (frei Γ reserved) cs ρ reserved →
      CountedReach ns L fp lo K pr ⟨pc, fp⟩ m
        (pc + BitVec.ofNat 64 (16 * cs.length)) σ1 ρ1 reserved)
    (restRuns : ∀ cr tr,
      lowB (reserved := reserved) passes A L (functionFrame P f) ens pr ex rest = some (cr, tr) →
      ∀ m' pc', PreS L m' pc' fp K (frei Γ reserved) cr ρ1 reserved →
      WeltAt m' L σ1 →
      CountedReach nr L fp lo K pr ⟨pc', fp⟩ m'
        (pc' + BitVec.ofNat 64 (16 * cr.length)) σ2 ρ2 reserved) :
    CountedReach (ns + nr) L fp lo K pr ⟨pc, fp⟩ m
      (pc + BitVec.ofNat 64 (16 * code.length)) σ2 ρ2 reserved := by
  simp only [lowB, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at lower
  obtain ⟨⟨cr, tr⟩, hr, ⟨cs, ts⟩, hs, out⟩ := lower
  simp only [Prod.mk.injEq] at out
  obtain ⟨rfl, rfl⟩ := out
  obtain ⟨m1, run1, agree1, env1, world1, keep1⟩ :=
    stmtRuns cr tr cs ts hr hs pre.left
  have far := codeFar_right (n := cs.length) (k := cr.length) (by simpa using pre.far)
  have nextPre : PreS L m1 (pc + BitVec.ofNat 64 (16 * cs.length)) fp K
      (frei Γ reserved) cr ρ1 reserved :=
    ⟨pre.ctx, pre.small, frameOK_agreeW pre.frame agree1,
      codeAt_agreeWIn inside agree1 (codeAt_right pre.code) far,
      far, env1, trivial, wstab_true _ _⟩
  obtain ⟨m2, run2, agree2, env2, world2, keep2⟩ :=
    restRuns cr tr hr m1 _ nextPre world1
  refine ⟨m2, ?_, agree1.trans agree2, env2, world2, keep1.trans keep2⟩
  simpa only [List.length_append, pc_add] using run1.trans run2

/-- A real lexical binding obtains its instruction count from the recursive
    expression certificate, then executes the actual lowered continuation.
    The source value is supplied through `Enc`, as in `bindValue_ok`. -/
theorem countedBlockBind_case
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty}
    {e : Expr D Γ Λ τ} {rest : Block D V l (τ :: Γ) Λ Λ'}
    {passes lo K Ks ne nr top : Nat} {A : D.Fn → Nat}
    {ens : List II × Nat} {pr : List Nat} {ex : Int × Int}
    {code : List II} {m : Runner.Mem} {pc fp : Runner.W}
    {ρ : Env D Γ} {v : Wert D τ} {ρ2 : Env D (τ :: Γ)} {σ σ2 : World D}
    (certificate : ExprCost L reserved e (frei Γ reserved) ne (Enc L τ v))
    (lower : lowB (reserved := reserved) passes A L (functionFrame P f) ens pr ex (.bind e rest) =
      some (code, top))
    (fits : top ≤ Ks) (inside : WIn L fp Ks K)
    (low : lo ≤ frei Γ reserved) (hprotected : ∀ j ∈ pr, j < frei Γ reserved)
    (pre : PreS L m pc fp K (frei Γ reserved) code ρ reserved)
    (world : WeltAt m L σ)
    (restRuns : ∀ cr tr,
      lowB (reserved := reserved) passes A L (functionFrame P f) ens pr ex rest = some (cr, tr) →
      ∀ m' pc', PreS L m' pc' fp K (frei (τ :: Γ) reserved) cr (Env.cons v ρ) reserved →
      WeltAt m' L σ →
      CountedReach nr L fp lo K pr ⟨pc', fp⟩ m'
        (pc' + BitVec.ofNat 64 (16 * cr.length)) σ2 ρ2 reserved) :
    CountedReach (ne + nr) L fp lo K pr ⟨pc, fp⟩ m
      (pc + BitVec.ofNat 64 (16 * code.length)) σ2 ρ2 reserved := by
  simp only [lowB, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at lower
  obtain ⟨⟨ce, te⟩, he, ⟨cr, tr⟩, hr, out⟩ := lower
  simp only [Prod.mk.injEq] at out
  obtain ⟨rfl, rfl⟩ := out
  have room := lowE_top e _ _ _ he
  have hks := inside.ks
  have hpw := PreS.welt pre.left inside.ks world inside.lay
    (by have := inside.lo; omega)
  obtain ⟨m1, run1, a1s, value⟩ := certificate.sound_value he
    (Nat.le_trans (Nat.le_max_left _ _) fits) hpw
  have a1 := Agree.widen a1s inside.ks
  have far := codeFar_right (n := ce.length) (k := cr.length) (by simpa using pre.far)
  have nextPre : PreS L m1 (pc + BitVec.ofNat 64 (16 * ce.length)) fp K
      (frei (τ :: Γ) reserved) cr (Env.cons v ρ) reserved :=
    ⟨by simp only [frei, contextWords_cons]; omega, pre.small, pre.frame.agree a1,
      (codeAt_right pre.code).agree a1 far, far,
      envAt_cons (envAt_agree pre.env a1 pre.frame (Nat.le_refl _) (by omega))
        value, trivial, wstab_true _ _⟩
  obtain ⟨m2, run2, a2, env2, world2, keep2⟩ := restRuns cr tr hr m1 _ nextPre
    (hpw.wstab m m1 world (a1s.mono (Nat.zero_le _)))
  refine ⟨m2, ?_, (agreeW_of (a1.mono low)).trans a2, env2, world2, ?_⟩
  · simpa only [List.length_append, pc_add] using run1.trans run2
  · exact (keeps_of_agreeW inside a1 hprotected (by omega)).trans keep2

/-- Count a real call opcode, the callee body, and the real return opcode.
    Return addresses and frame restoration are read from the resulting callee
    memory, so a body that corrupts the ABI cannot satisfy this rule. -/
theorem countedCall {t u : T} {m m1 m2 m3 : Runner.Mem}
    {a k c ra rb rc : BitVec 32} {target : Runner.W} {n : Nat}
    (callCode : InsAt m t.pc 20 a k c)
    (targetRead : m.rd64 (slot t.fp (sx a)) = some target)
    (savePC : m.wr64 (slot t.fp (sx k)) (t.pc + 16) = some m1)
    (saveFP : m1.wr64 (slot t.fp (sx k) + 8) t.fp = some m2)
    (callee : Counted n ⟨target, slot t.fp (sx k)⟩ m2 u m3)
    (returnCode : InsAt m3 u.pc 21 ra rb rc)
    (returnPC : m3.rd64 u.fp = some (t.pc + 16))
    (returnFP : m3.rd64 (u.fp + 8) = some t.fp) :
    Counted (n + 2) t m ⟨t.pc + 16, t.fp⟩ m3 := by
  have enter : Counted 1 t m ⟨target, slot t.fp (sx k)⟩ m2 :=
    .next (run_step callCode (by decide)
      (run_call callCode targetRead savePC saveFP)) (.refl _ _)
  have leave : Counted 1 u m3 ⟨t.pc + 16, t.fp⟩ m3 :=
    .next (run_step returnCode (by decide) (run_ret returnPC returnFP)) (.refl _ _)
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using (enter.trans callee).trans leave

/-- A returning expression callee derives its execution count recursively from
    the source certificate. Agreement proves preservation of both ABI cells
    and the return instruction; no post-body ABI or execution premise is used.
    This is an instruction count, not a conversion from declared G costs. -/
theorem ExprCost.returning {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    {e : Expr D Γ Λ τ} {d n top K : Nat} {P : Runner.W → Prop}
    (certificate : ExprCost L reserved e d n P)
    {code : List II} {m : Runner.Mem} {pc fp resume caller : Runner.W}
    {ρ : Env D Γ} {W : Runner.Mem → Prop}
    (lower : lowE L (reserved := reserved) e d = some (code, top))
    (fits : top ≤ K) (abi : 2 ≤ d) (room : d ≤ K)
    (pre : Pre L m pc fp K d code ρ W reserved)
    (ret : CodeAt m (pc + BitVec.ofNat 64 (16 * code.length)) [ci 21 0 0 0])
    (far : CodeFar (pc + BitVec.ofNat 64 (16 * code.length)) 1 fp K)
    (savedPC : m.rd64 fp = some resume)
    (savedFP : m.rd64 (fp + 8) = some caller) :
    ∃ m', Counted (n + 1) ⟨pc, fp⟩ m ⟨resume, caller⟩ m' ∧
      Agree fp d K m m' ∧
      ∃ w, m'.rd64 (slot fp (BitVec.ofNat 64 d)) = some w ∧ P w := by
  obtain ⟨m', run, agree, value⟩ := certificate.sound lower fits pre
  have ret' := (ret.agree agree far) 0 (by simp)
  simp only [List.getElem_cons_zero, ci, Nat.mul_zero, BitVec.add_zero] at ret'
  have rpc : m'.rd64 fp = some resume := by
    have h := agree_rd_low (i := 0) agree pre.frame.room (by omega) room
    simp only [slot, BitVec.zero_mul, BitVec.add_zero] at h
    exact h.trans savedPC
  have rfp : m'.rd64 (fp + 8) = some caller := by
    have h := agree_rd_low (i := 1) agree pre.frame.room (by omega) room
    have h' : m'.rd64 (fp + 8) = m.rd64 (fp + 8) := by simpa [slot] using h
    exact h'.trans savedFP
  refine ⟨m', ?_, agree, value⟩
  have leave : Counted 1 ⟨pc + BitVec.ofNat 64 (16 * code.length), fp⟩ m'
      ⟨resume, caller⟩ m' :=
    .next (run_step ret' (by decide) (run_ret rpc rfp)) (.refl _ _)
  exact run.trans leave

/-- A checked declaration table in S0IR instruction units for returning
    expression bodies. The exact body cost is derived by `ExprCost`, not
    assumed as an execution premise. The table includes the return opcode;
    the caller's call opcode remains an additional instruction. This is
    independent of `kostenPasst`, whose table counts G own steps. -/
structure CalleeCostCertificate (L : Lay D) (declared : D.Fn → Nat)
    (f : D.Fn) {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    (reserved : Nat) (e : Expr D Γ Λ τ) (d : Nat)
    (P : Runner.W → Prop) where
  instructions : Nat
  body : ExprCost L reserved e d instructions P
  within : instructions + 1 ≤ declared f

theorem CalleeCostCertificate.returning {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    {e : Expr D Γ Λ τ} {d top K : Nat} {declared : D.Fn → Nat} {f : D.Fn} {P : Runner.W → Prop}
    (certificate : CalleeCostCertificate L declared f reserved e d P)
    {code : List II} {m : Runner.Mem} {pc fp resume caller : Runner.W}
    {ρ : Env D Γ} {W : Runner.Mem → Prop}
    (lower : lowE L (reserved := reserved) e d = some (code, top))
    (fits : top ≤ K) (abi : 2 ≤ d) (room : d ≤ K)
    (pre : Pre L m pc fp K d code ρ W reserved)
    (ret : CodeAt m (pc + BitVec.ofNat 64 (16 * code.length)) [ci 21 0 0 0])
    (far : CodeFar (pc + BitVec.ofNat 64 (16 * code.length)) 1 fp K)
    (savedPC : m.rd64 fp = some resume)
    (savedFP : m.rd64 (fp + 8) = some caller) :
    ∃ n m', n ≤ declared f ∧ Counted n ⟨pc, fp⟩ m ⟨resume, caller⟩ m' ∧
      Agree fp d K m m' ∧
      ∃ w, m'.rd64 (slot fp (BitVec.ofNat 64 d)) = some w ∧ P w := by
  obtain ⟨m', run, rest⟩ := certificate.body.returning lower fits abi room pre ret far savedPC savedFP
  exact ⟨certificate.instructions + 1, m', certificate.within, run, rest⟩

/-- Declaration-bound execution through the actual call ABI. The entry writes
    are checked before the source-derived callee certificate is applied to the
    resulting memory. The bound includes call and return, in S0IR instructions;
    `Kern` remains the explicit canonical hardware interface. -/
theorem CalleeCostCertificate.call {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    {e : Expr D Γ Λ τ} {d top K : Nat} {declared : D.Fn → Nat} {f : D.Fn}
    {P : Runner.W → Prop}
    (certificate : CalleeCostCertificate L declared f reserved e d P)
    {code : List II} {m m1 m2 : Runner.Mem} {t : T}
    {a k c : BitVec 32} {target : Runner.W}
    {ρ : Env D Γ} {W : Runner.Mem → Prop}
    (callCode : InsAt m t.pc 20 a k c)
    (targetRead : m.rd64 (slot t.fp (sx a)) = some target)
    (savePC : m.wr64 (slot t.fp (sx k)) (t.pc + 16) = some m1)
    (saveFP : m1.wr64 (slot t.fp (sx k) + 8) t.fp = some m2)
    (lower : lowE L (reserved := reserved) e d = some (code, top))
    (fits : top ≤ K) (abi : 2 ≤ d) (room : d ≤ K)
    (pre : Pre L m2 target (slot t.fp (sx k)) K d code ρ W reserved)
    (ret : CodeAt m2 (target + BitVec.ofNat 64 (16 * code.length)) [ci 21 0 0 0])
    (far : CodeFar (target + BitVec.ofNat 64 (16 * code.length)) 1
      (slot t.fp (sx k)) K)
    (savedPC : m2.rd64 (slot t.fp (sx k)) = some (t.pc + 16))
    (savedFP : m2.rd64 (slot t.fp (sx k) + 8) = some t.fp) :
    ∃ n m', n ≤ declared f + 1 ∧ Counted n t m ⟨t.pc + 16, t.fp⟩ m' ∧
      Agree (slot t.fp (sx k)) d K m2 m' ∧
      ∃ w, m'.rd64 (slot (slot t.fp (sx k)) (BitVec.ofNat 64 d)) = some w ∧ P w := by
  obtain ⟨n, m', bound, run, rest⟩ := certificate.returning lower fits abi room
    pre ret far savedPC savedFP
  have enter : Counted 1 t m ⟨target, slot t.fp (sx k)⟩ m2 :=
    .next (run_step callCode (by decide)
      (run_call callCode targetRead savePC saveFP)) (.refl _ _)
  exact ⟨1 + n, m', by omega, enter.trans run, rest⟩

/-- Compose any finite family of actual execution segments. Segment bounds
    must include the invariant, body/callees, header, backedge and exits as
    applicable; no code-length assumption is made for a recursive segment. -/
inductive CountedSegments : List Nat → T → Mem → T → Mem → Prop
  | nil (t m) : CountedSegments [] t m t m
  | cons {ns n t u v m a b} : Counted n t m u a →
      CountedSegments ns u a v b → CountedSegments (n :: ns) t m v b

end Gabbro.Stage0.Senke
