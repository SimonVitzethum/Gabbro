module

public import Stage0.Senke.Anweisung.Simulation
public import Stage0.Senke.Ausdruck.Gleichungen
public import Stage0.Senke.Anweisung.Faelle.Schleifen.Counted.Teil1

@[expose] public section

namespace Gabbro.Stage0.Senke
open Runner Runner.IR
variable [Kern]
open Gabbro.Grammatik Runner.Mem
variable {D : Deklaration} {L : Lay D} {reserved : Nat}

/-- A counted expression result carries the same complete typed memory relation
    as ordinary lowering. Scalar specializations are proved through Enc.single. -/
def CountedValueOk (n : Nat) (L : Lay D) (m : Mem) (pc fp : W) (K d : Nat)
    (code : List II) (τ : Ty) (v : Wert D τ) : Prop :=
  ∃ m', Counted n ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * code.length), fp⟩ m' ∧
    Agree fp d K m m' ∧ ValueAt L m' fp d τ v

theorem lowE_literal_value_counted {Γ : Ctx} {Λ : List (Res D)} {k : Int}
    (v : Zahl k k) {d top K : Nat} {code : List II} {m : Mem} {pc fp : W}
    {ρ : Env D Γ} {W : Mem → Prop}
    (lower : lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (.lit k) d = some (code, top))
    (fits : top ≤ K) (pre : Pre L m pc fp K d code ρ W reserved) :
    CountedValueOk (literalCount k d) L m pc fp K d code (.int k k) v := by
  have number : v.n = k := by have := v.lo_le; have := v.le_hi; omega
  rw [lowE_lit] at lower
  split at lower
  · next small =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj lower)
    obtain ⟨m', run, changed, w, read, encoded⟩ := const_counted_ok small (by omega) pre
    refine ⟨m', by simpa only [literalCount, small, ite_true] using run,
      changed, ValueAt.of_enc ?_ read ?_⟩
    · have bounds := small
      simp only [lit32, Bool.and_eq_true, decide_eq_true_eq] at bounds
      exact integerWords_word (by omega) (by omega)
    · simpa only [Enc, number] using encoded
  · next large =>
    have pair := Option.some.inj lower
    have codeEq := congrArg Prod.fst pair
    have topEq := congrArg Prod.snd pair
    dsimp only at codeEq topEq
    subst code
    subst top
    obtain ⟨m', run, changed, output⟩ := constWords_counted
      (integerEncoding (integerWords k k) k) fits pre
    refine ⟨m', ?_, changed, trivial, ?_⟩
    · simpa only [literalCount, large, Bool.false_eq_true, ↓reduceIte, encodeWords] using run
    · simpa only [encodeWords, number] using output

theorem ExprCost.sound_value {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    {e : Expr D Γ Λ τ} {d n : Nat} {v : Wert D τ}
    (certificate : ExprCost L reserved e d n (Enc L τ v))
    {code : List II} {top K : Nat} {m : Mem} {pc fp : W}
    {ρ : Env D Γ} {W : Mem → Prop}
    (lower : lowE L (reserved := reserved) e d = some (code, top))
    (fits : top ≤ K) (pre : Pre L m pc fp K d code ρ W reserved) :
    CountedValueOk n L m pc fp K d code τ v := by
  rcases certificate.width_or_literal lower with width | ⟨k, sameType, sameExpr, count⟩
  · obtain ⟨m', run, changed, w, read, encoded⟩ := certificate.sound lower fits pre
    exact ⟨m', run, changed, ValueAt.of_enc width read encoded⟩
  · subst τ
    cases sameExpr
    subst n
    exact lowE_literal_value_counted v lower fits pre

/-- Quantitative normal block outcome, retaining the same world, environment
    and protected-slot obligations as `Reach`. -/
def CountedReach (n : Nat) (L : Lay D) {Γ : Ctx} (fp : Runner.W)
    (lo K : Nat) (pr : List Nat) (t : T) (m : Runner.Mem)
    (e : Runner.W) (σ : World D) (ρ : Env D Γ) (reserved : Nat := 0) : Prop :=
  ∃ m', Counted n t m ⟨e, fp⟩ m' ∧ AgreeW L fp lo K m m' ∧
    EnvAt L m' fp ρ reserved ∧ WeltAt m' L σ ∧ Keeps fp pr m m'

theorem CountedReach.forget {n Γ fp lo K pr t m e σ ρ reserved}
    (h : CountedReach n L (Γ := Γ) fp lo K pr t m e σ ρ reserved) :
    Reach L fp lo K pr t m e σ ρ reserved := by
  obtain ⟨m', run, rest⟩ := h
  exact ⟨m', run.forget, rest⟩

/-- A counted pending hardware request; no hardware completion is asserted. -/
def CountedStops (n : Nat) (t : T) (m : Mem) (c : Nat) : Prop :=
  ∃ t' m' q, Counted n t m t' m' ∧ StopAt t' m' q ∧
    q.nr = 231 ∧ q.a1 = BitVec.ofNat 64 c

theorem CountedStops.forget {n t m c} (h : CountedStops n t m c) : Stops t m c := by
  obtain ⟨t', m', q, run, rest⟩ := h
  exact ⟨t', m', q, run.forget, rest⟩

/-- Return costs use the caller endpoint and the canonical return ABI. -/
def CountedRetZ (n : Nat) (L : Lay D) (P : Programm D) (f : D.Fn) (σ0 : World D) (ρ0 : Env D (D.params f)) (fp : Runner.W) (K : Nat)
    (rp cfp : Runner.W) (t : T) (m : Runner.Mem) (σ' : World D) (v : ErgVal D (D.erg f)) : Prop :=
  if returnFault P f σ0 σ' ρ0 v ≠ 0
  then CountedStops n t m (returnFault P f σ0 σ' ρ0 v)
  else ∃ m', Counted n t m ⟨rp, cfp⟩ m' ∧ AgreeW L fp 2 K m m' ∧
    (ResultAt L m' fp (FB + contextWords (D.params f)) (D.erg f) v ∧
      ReturnMirror m' fp (FB + contextWords (D.params f)) ∧
      ReturnFlag m' fp (contextWords (D.params f)) true (returnWords (D.erg f) (D.gruende f))) ∧
      WeltAt m' L (owedWorld P f (σ'.lese (vertragVon D f).ende (P.ensures f).orte))

def CountedRetWhy (n : Nat) (L : Lay D) (f : D.Fn) (fp : Runner.W) (K : Nat) (rp cfp : Runner.W)
    (t : T) (m : Runner.Mem) (σ : World D) (r : Fin (D.gruende f)) : Prop :=
  ∃ m', Counted n t m ⟨rp, cfp⟩ m' ∧ AgreeW L fp 2 K m m' ∧
    ValueAt L m' fp (FB + contextWords (D.params f)) (.why (D.gruende f)) r ∧
    ReturnMirror m' fp (FB + contextWords (D.params f)) ∧
    ReturnFlag m' fp (contextWords (D.params f)) false (returnWords (D.erg f) (D.gruende f)) ∧ WeltAt m' L σ

def CountedSim (n : Nat) (L : Lay D) (P : Programm D) (f : D.Fn) (σ0 : World D) (ρ0 : Env D (D.params f)) (rp cfp : Runner.W)
    {l : Bool} {Γ : Ctx} (fp : Runner.W) (lo K : Nat) (pr : List Nat) (t : T) (m : Runner.Mem) (e eL eN : Runner.W) (o : Ausgang (vertragVon D f) l Γ) (reserved : Nat := 0) : Prop :=
  match o with
  | .ok σ' ρ' => CountedReach n L fp lo K pr t m e σ' ρ' reserved
  | .leave _ σ' ρ' => CountedReach n L fp lo K pr t m eL σ' ρ' reserved
  | .next _ σ' ρ' => CountedReach n L fp lo K pr t m eN σ' ρ' reserved
  | .zurueck σ' v => CountedRetZ n L P f σ0 ρ0 fp K rp cfp t m σ' v
  | .logik c => CountedStops n t m (logikCode c)
  | .hardware h => CountedStops n t m (hwCode h)
  | .why σ' r => CountedRetWhy n L f fp K rp cfp t m σ' r
theorem CountedRetZ.forget {n P f σ0 ρ0 fp K rp cfp t m σ v}
    (h : CountedRetZ n L P f σ0 ρ0 fp K rp cfp t m σ v) :
    RetZ L P f σ0 ρ0 fp K rp cfp t m σ v := by
  unfold CountedRetZ at h
  unfold RetZ
  split at h
  · rename_i hp
    rw [if_pos hp]
    exact h.forget
  · rename_i hp
    rw [if_neg hp]
    obtain ⟨m', run, rest⟩ := h
    exact ⟨m', run.forget, rest⟩

theorem CountedRetWhy.forget {n f fp K rp cfp t m σ r}
    (h : CountedRetWhy n L f fp K rp cfp t m σ r) :
    RetWhy L f fp K rp cfp t m σ r := by
  obtain ⟨m', run, rest⟩ := h
  exact ⟨m', run.forget, rest⟩

/-- Erasure preserves precisely the existing simulation outcome index. -/
theorem CountedSim.forget {n P f σ0 ρ0 rp cfp l Γ fp lo K pr t m e eL eN reserved}
    {o : Ausgang (vertragVon D f) l Γ}
    (h : CountedSim n L P f σ0 ρ0 rp cfp fp lo K pr t m e eL eN o reserved) :
    Sim L P f σ0 ρ0 rp cfp fp lo K pr t m e eL eN o reserved := by
  cases o with
  | ok σ ρ => exact CountedReach.forget h
  | leave _ σ ρ => exact CountedReach.forget h
  | next _ σ ρ => exact CountedReach.forget h
  | zurueck σ v => exact CountedRetZ.forget h
  | why σ r => exact CountedRetWhy.forget h
  | logik c => exact CountedStops.forget h
  | hardware c => exact CountedStops.forget h

/-- Prefix composition keeps the counted endpoint and all observations joint. -/
theorem CountedReach.prefix {n k Γ fp lo K pr t0 t m0 m e σ ρ reserved}
    (run : Counted k t0 m0 t m) (agree : AgreeW L fp lo K m0 m)
    (keep : Keeps fp pr m0 m)
    (h : CountedReach n L (Γ := Γ) fp lo K pr t m e σ ρ reserved) :
    CountedReach (k + n) L fp lo K pr t0 m0 e σ ρ reserved := by
  obtain ⟨m', tail, frame, env, world, kept⟩ := h
  exact ⟨m', run.trans tail, agree.trans frame, env, world, keep.trans kept⟩

theorem CountedStops.prefix {n k t0 t m0 m c}
    (run : Counted k t0 m0 t m) (h : CountedStops n t m c) :
    CountedStops (k + n) t0 m0 c := by
  obtain ⟨t', m', q, tail, rest⟩ := h
  exact ⟨t', m', q, run.trans tail, rest⟩

theorem CountedRetZ.prefix {n k : Nat} {L : Lay D} {P : Programm D} {f : D.Fn} {σ0 : World D} {ρ0 : Env D (D.params f)} {fp : Runner.W}
    {K : Nat} {rp cfp : Runner.W} {t0 t : T} {m0 m : Runner.Mem} {σ' : World D} {v : ErgVal D (D.erg f)}
    (h : Counted k t0 m0 t m) (ha : AgreeW L fp 2 K m0 m) (hs : CountedRetZ n L P f σ0 ρ0 fp K rp cfp t m σ' v) :
    CountedRetZ (k + n) L P f σ0 ρ0 fp K rp cfp t0 m0 σ' v := by
  simp only [CountedRetZ] at hs ⊢
  split
  · next hf => rw [if_pos hf] at hs; exact CountedStops.prefix h hs
  · next hf =>
    rw [if_neg hf] at hs
    obtain ⟨m', s, a, hw, hw'⟩ := hs
    exact ⟨m', h.trans s, ha.trans a, hw, hw'⟩

theorem CountedRetWhy.prefix {n k : Nat} {f : D.Fn} {fp : Runner.W} {K : Nat} {rp cfp : Runner.W}
    {t0 t : T} {m0 m : Runner.Mem} {σ : World D} {r : Fin (D.gruende f)}
    (h : Counted k t0 m0 t m) (ha : AgreeW L fp 2 K m0 m) (hs : CountedRetWhy n L f fp K rp cfp t m σ r) :
    CountedRetWhy (k + n) L f fp K rp cfp t0 m0 σ r := by
  obtain ⟨m', s, a, hw, flag, hw'⟩ := hs
  exact ⟨m', h.trans s, ha.trans a, hw, flag, hw'⟩

theorem CountedSim.prefix {n k : Nat} {P : Programm D} {f : D.Fn} {σ0 : World D}
    {ρ0 : Env D (D.params f)} {rp cfp fp : W} {l : Bool} {Γ : Ctx}
    {lo K reserved : Nat} {pr : List Nat} {o : Ausgang (vertragVon D f) l Γ} {t0 t : T} {m0 m : Runner.Mem} {e eL eN : Runner.W}
    (hl : FB ≤ lo) (h : Counted k t0 m0 t m) (ha : AgreeW L fp lo K m0 m) (hk : Keeps fp pr m0 m)
    (hs : CountedSim n L P f σ0 ρ0 rp cfp fp lo K pr t m e eL eN o reserved) : CountedSim (k + n) L P f σ0 ρ0 rp cfp fp lo K pr t0 m0 e eL eN o reserved := by
  cases o with
  | ok σ ρ => exact CountedReach.prefix h ha hk hs
  | leave _ σ ρ => exact CountedReach.prefix h ha hk hs
  | next _ σ ρ => exact CountedReach.prefix h ha hk hs
  | zurueck σ' v =>
    have hFB3 : FB = 4 := rfl
    exact CountedRetZ.prefix h (ha.mono (by omega)) hs
  | logik c => exact CountedStops.prefix h hs
  | hardware c => exact CountedStops.prefix h hs
  | why σ' r => exact CountedRetWhy.prefix h (ha.mono (by have : FB = 4 := rfl; omega)) hs

/-- Both source loop jumps retain one joint state and execute exactly one
    instruction. The signed displacement is justified by accepted lowering. -/
theorem jmp_counted_reach {Γ : Ctx} {m : Mem} {pc fp : W}
    {lo K reserved : Nat} {pr : List Nat} {x : Int}
    {σ : World D} {ρ : Env D Γ}
    (code : CodeAt m pc [ci 18 (16 + x) 0 0])
    (fits : lit32 (16 + x) = true)
    (env : EnvAt L m fp ρ reserved) (world : WeltAt m L σ) :
    CountedReach 1 L fp lo K pr ⟨pc, fp⟩ m
      (pc + 16 + BitVec.ofInt 64 x) σ ρ reserved := by
  have ins := code 0 (by simp)
  simp only [ci, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at ins
  have run := Counted.next (run_step (t := ⟨pc, fp⟩) ins (by decide)
    (run_jmp (t := ⟨pc, fp⟩) ins)) (Counted.refl _ _)
  refine ⟨m, ?_, AgreeW.refl _ _ _ _ _, env, world, Keeps.refl _ _ _⟩
  simpa only [sx_lit fits, BitVec.ofInt_add, BitVec.add_assoc,
    show BitVec.ofInt 64 16 = (16 : W) from rfl] using run

/-- Empty blocks execute no instructions and preserve the entire state. -/
theorem countedBlockNil_case {Γ : Ctx} {fp pc : Runner.W} {lo K : Nat}
    {pr : List Nat} {m : Runner.Mem} {σ : World D} {ρ : Env D Γ}
    (env : EnvAt L m fp ρ reserved) (world : WeltAt m L σ) :
    CountedReach 0 L fp lo K pr ⟨pc, fp⟩ m pc σ ρ reserved :=
  ⟨m, .refl _ _, AgreeW.refl _ _ _ _ _, env, world, Keeps.refl _ _ _⟩

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
