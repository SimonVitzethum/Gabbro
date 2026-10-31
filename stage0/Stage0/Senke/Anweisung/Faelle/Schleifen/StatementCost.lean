/- Source-bound instruction costs for actual statement lowering. -/
import Stage0.Senke.Anweisung.Faelle.Schleifen.Counted
import Stage0.Senke.Anweisung.Hilfe
import Stage0.Senke.Ausdruck.FnptrAufrufProben

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner Runner.IR Runner.Mem
variable [Kern]
variable {D : Deklaration} {L : Lay D} {reserved : Nat}
set_option maxHeartbeats 2000000

/-- The emitted variable move completes one instruction. -/
theorem mov_to_counted {m : Mem} {pc fp : W} {K j s : Nat} {w : W}
    (hc : CodeAt m pc [ci 2 j s 0]) (hF : FrameOK m fp K)
    (hj : j < K) (hs : s < K) (hK : K < 2 ^ 31)
    (hv : m.rd64 (slot fp (BitVec.ofNat 64 s)) = some w) :
    Counted 1 ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * [ci 2 j s 0].length), fp⟩
      (write m (slot fp (BitVec.ofNat 64 j)) 8 w.toNat) := by
  have hi := hc 0 (by simp)
  simp only [ci, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at hi
  apply counted_ins hc (by simp [ci])
  simp only [ci, op]
  refine f2_run (t := ⟨pc, fp⟩) hi ?_
  rw [sx_nat (by omega)]
  refine run_rd64 hv ?_
  simp only [ret1]
  refine f1_run (t := ⟨pc, fp⟩) hi ?_
  rw [sx_nat (by omega)]
  exact run_wr64 (wr64_some (hF.wr j hj))

/-- Assignment cost comes from its expression tree and the actual move.
    The result retains the changed source environment and unchanged world. -/
theorem countedAssignVar_case
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {τ : Ty} {x : Var Γ τ} {e : Expr D Γ Λ τ}
    {passes lo K Ks ne top : Nat} {A : D.Fn → Nat}
    {ens : List II × Nat} {pr : List Nat} {ex : Int × Int}
    {code : List II} {m : Mem} {pc fp : W}
    {ρ : Env D Γ} {v : Wert D τ} {σ : World D}
    (certificate : ExprCost L reserved e (frei Γ reserved) ne (Enc L τ v))
    (lower : lowS (V := V) (l := l) (reserved := reserved)
      passes A L lo ens pr ex (.assignVar x e) = some (code, top))
    (fits : top ≤ Ks) (inside : WIn L fp Ks K)
    (low : lo ≤ frei Γ reserved) (hprotected : ∀ j ∈ pr, j < frei Γ reserved)
    (pre : PreS L m pc fp K (frei Γ reserved) code ρ reserved)
    (world : WeltAt m L σ) :
    CountedReach (ne + 1) L fp lo K pr ⟨pc, fp⟩ m
      (pc + BitVec.ofNat 64 (16 * code.length)) σ (ρ.set x v) reserved := by
  simp only [lowS] at lower
  split at lower
  next allowed =>
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at lower
    obtain ⟨⟨ce, te⟩, he, out⟩ := lower
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj out
    have hks := inside.ks
    have room := lowE_top e _ _ _ he
    have hpw := PreS.welt pre.left hks world inside.lay (by have := inside.lo; omega)
    obtain ⟨m1, run1, a1s, w, read, encoded⟩ := certificate.sound he fits hpw
    have a1 := Agree.widen a1s hks
    have hp1 := pre.next a1 (Nat.le_refl _) (by omega)
    have hxs := vslot_lt (reserved := reserved) x
    have hF1 := hp1.frame
    have run2 := mov_to_counted hp1.code hF1 (j := vslot x reserved)
      (by omega) (by omega) pre.small read
    have a2s : Agree fp lo Ks m1 _ :=
      agree_write (frameOK_sub hF1 hks).room allowed.1 (by omega) w.toNat
    refine ⟨_, ?_, agreeW_of ((a1.mono low).trans (Agree.widen a2s hks)), ?_,
      hpw.wstab m _ world ((a1s.mono (Nat.zero_le _)).trans (a2s.mono (Nat.zero_le _))),
      (keeps_of_agreeW inside a1 hprotected (by omega)).trans
        (keeps_write hF1.room (by omega) (fun j hj => by have := hprotected j hj; omega) allowed.2 _)⟩
    · rw [pc_add1]; exact run1.trans run2
    · refine envAt_set hp1.env
        (rd64_wr64 (wr64_some (hF1.wr _ (by omega))) (hF1.rd _ (by omega))) encoded ?_
      intro τ' y hy
      have := vslot_lt (reserved := reserved) y
      exact rd64_write_far (slot_far hF1.room (by omega) (by omega) (vslot_ne hy).symm)
  next refused => simp at lower

/-- Recursive source certificate for normal block outcomes. Only constructors
    with proved lowering costs are admitted; there is no arbitrary-run leaf.
    Both source states are indices, so cons threads the actual changed world
    and environment instead of silently restoring the entry state. -/
inductive BlockCost (L : Lay D) (reserved : Nat) (V : Vertrag D) (l : Bool) :
    {Γ : Ctx} → {Λ Λ' : List (Res D)} → Block D V l Γ Λ Λ' →
      World D → Env D Γ → World D → Env D Γ → Nat → Type
  | nil {Γ Λ σ} {ρ : Env D Γ} :
      BlockCost L reserved V l (.nil (Λ := Λ)) σ ρ σ ρ 0
  | assign {Γ Λ τ} {x : Var Γ τ} {e : Expr D Γ Λ τ}
      {rest : Block D V l Γ Λ Λ} {σ σ' : World D}
      {ρ ρ' : Env D Γ} {v : Wert D τ} {ne nr : Nat}
      (value : ExprCost L reserved e (frei Γ reserved) ne (Enc L τ v))
      (tail : BlockCost L reserved V l rest σ (ρ.set x v) σ' ρ' nr) :
      BlockCost L reserved V l (.cons (.assignVar x e) rest) σ ρ σ' ρ' (ne + 1 + nr)

  | bind {Γ Λ Λ' τ} {e : Expr D Γ Λ τ}
      {rest : Block D V l (τ :: Γ) Λ Λ'} {σ σ' : World D}
      {ρ : Env D Γ} {ρ' : Env D (τ :: Γ)} {v : Wert D τ} {ne nr : Nat}
      (value : ExprCost L reserved e (frei Γ reserved) ne (Enc L τ v))
      (tail : BlockCost L reserved V l rest σ (.cons v ρ) σ' ρ' nr) :
      BlockCost L reserved V l (.bind e rest) σ ρ σ' ρ'.tail (ne + nr)

/-- Every count is derived from an accepted source lowering. The only
    additional obligations are the existing frame/layout/world conditions. -/
theorem BlockCost.sound {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {b : Block D V l Γ Λ Λ'}
    {σ σ' : World D} {ρ ρ' : Env D Γ} {n : Nat}
    (certificate : BlockCost L reserved V l b σ ρ σ' ρ' n)
    {passes lo K Ks top : Nat} {A : D.Fn → Nat} {ens : List II × Nat}
    {pr : List Nat} {ex : Int × Int} {code : List II}
    {m : Mem} {pc fp : W}
    (lower : lowB (reserved := reserved) passes A L lo ens pr ex b = some (code, top))
    (fits : top ≤ Ks) (inside : WIn L fp Ks K)
    (low : lo ≤ frei Γ reserved) (hprotected : ∀ j ∈ pr, j < frei Γ reserved)
    (pre : PreS L m pc fp K (frei Γ reserved) code ρ reserved)
    (world : WeltAt m L σ) :
    CountedReach n L fp lo K pr ⟨pc, fp⟩ m
      (pc + BitVec.ofNat 64 (16 * code.length)) σ' ρ' reserved := by
  induction certificate generalizing top code m pc ex with
  | nil =>
    simp only [lowB, Option.some.injEq, Prod.mk.injEq] at lower
    obtain ⟨rfl, rfl⟩ := lower
    simpa using countedBlockNil_case (L := L) (lo := lo) (pr := pr) pre.env world
  | assign value tail ih =>
    have decoded := lower
    simp only [lowB, Bind.bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at decoded
    obtain ⟨⟨cr0, tr0⟩, hr0, ⟨cs0, ts0⟩, hs0, out⟩ := decoded
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj out
    apply countedBlockCons_case lower inside pre
    · intro cr tr cs ts hr hs hp
      rw [hr0] at hr
      cases hr
      rw [hs0] at hs
      cases hs
      exact countedAssignVar_case value hs0
        (Nat.le_trans (Nat.le_max_left _ _) fits) inside low hprotected hp world
    · intro cr tr hr m' pc' hp hw
      rw [hr0] at hr
      cases hr
      exact ih hr0 (Nat.le_trans (Nat.le_max_right _ _) fits) low hprotected hp hw
  | bind value tail ih =>
    have decoded := lower
    simp only [lowB, Bind.bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at decoded
    obtain ⟨⟨ce0, te0⟩, he0, ⟨cr0, tr0⟩, hr0, out⟩ := decoded
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj out
    have result := countedBlockBind_case value lower fits inside low hprotected pre world
      (fun cr tr hr m' pc' hp hw => by
        rw [hr0] at hr
        cases hr
        apply ih hr0 (Nat.le_trans (Nat.le_max_right _ _) fits) ?_ ?_ hp hw
        · simp only [frei, List.length_cons] at low ⊢; omega
        · intro j hj
          have h := hprotected j hj
          simp only [frei, List.length_cons] at h ⊢; omega)
    obtain ⟨m', run, agree, env, world', keep⟩ := result
    exact ⟨m', run, agree, envAt_tail env, world', keep⟩

/-- Actual `lowEnd .cons` threads a normal statement outcome into a terminal
    continuation. The continuation can return to its caller or stop in a
    nested loop; it need not fall through to the end of the instruction list.
    Its cost is a recursive child obligation, never a bound on the whole body. -/
theorem countedEndCons_case
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λmid : List (Res D)}
    {s : Stmt D V l Γ Λ Λmid} {rest : Endblock D V l Γ Λmid}
    {passes lo K Ks ns nr top : Nat} {A : D.Fn → Nat}
    {ens : List II × Nat} {pr : List Nat} {ex : Int × Int}
    {code : List II} {m : Mem} {pc fp : W}
    {ρ ρ1 : Env D Γ} {σ1 : World D} {Done : T → Mem → Prop}
    (lower : lowEnd (reserved := reserved) passes A L lo ens pr ex (.cons s rest) =
      some (code, top))
    (inside : WIn L fp Ks K)
    (pre : PreS L m pc fp K (frei Γ reserved) code ρ reserved)
    (stmtRuns : ∀ cr tr cs ts,
      lowEnd (reserved := reserved) passes A L lo ens pr ex rest = some (cr, tr) →
      lowS (reserved := reserved) passes A L lo ens pr (exPlus ex cr.length) s = some (cs, ts) →
      PreS L m pc fp K (frei Γ reserved) cs ρ reserved →
      CountedReach ns L fp lo K pr ⟨pc, fp⟩ m
        (pc + BitVec.ofNat 64 (16 * cs.length)) σ1 ρ1 reserved)
    (restRuns : ∀ cr tr,
      lowEnd (reserved := reserved) passes A L lo ens pr ex rest = some (cr, tr) →
      ∀ m' pc', PreS L m' pc' fp K (frei Γ reserved) cr ρ1 reserved →
      WeltAt m' L σ1 → ∃ u b, Counted nr ⟨pc', fp⟩ m' u b ∧ Done u b) :
    ∃ u b, Counted (ns + nr) ⟨pc, fp⟩ m u b ∧ Done u b := by
  simp only [lowEnd, Bind.bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at lower
  obtain ⟨⟨cr, tr⟩, hr, ⟨cs, ts⟩, hs, out⟩ := lower
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj out
  obtain ⟨m1, run1, agree1, env1, world1, keep1⟩ :=
    stmtRuns cr tr cs ts hr hs pre.left
  have far := codeFar_right (n := cs.length) (k := cr.length) (by simpa using pre.far)
  have nextPre : PreS L m1 (pc + BitVec.ofNat 64 (16 * cs.length)) fp K
      (frei Γ reserved) cr ρ1 reserved :=
    ⟨pre.ctx, pre.small, frameOK_agreeW pre.frame agree1,
      codeAt_agreeWIn inside agree1 (codeAt_right pre.code) far,
      far, env1, trivial, wstab_true _ _⟩
  obtain ⟨u, b, run2, done⟩ := restRuns cr tr hr m1 _ nextPre world1
  exact ⟨u, b, run1.trans run2, done⟩

namespace BlockCostProbe
/-- A genuine nonempty statement body under a lexical binding. -/
def body (V : Vertrag D) : Block D V false [] [] [] :=
  .bind (.lit 2) (.cons (.assignVar .here (.lit 2)) .nil)

omit [Kern] in
/-- The count is derived from source constructors: binding, literal and move.
    This witness covers assignment blocks, not calls or nested forever. -/
theorem block_certificate_zeuge (V : Vertrag D) (σ : World D) :
    Nonempty (BlockCost L reserved V false (body V) σ .nil σ .nil 3) := by
  let v : Wert D (.int 2 2) := ⟨2, by decide, by decide⟩
  have value {Γ : Ctx} (d : Nat) :
      ExprCost L reserved (Γ := Γ) (Λ := []) (.lit 2) d 1 (Enc L (.int 2 2) v) :=
    .literal
  exact ⟨.bind (value _) (.assign (value _) .nil)⟩

open FnptrProben in
def image : List II := [ci 1 4 2 0, ci 1 5 2 0, ci 2 4 5 0]

open FnptrProben in
def memory : Mem := { callMem with
  b := fun a => if a.toNat < 48 then
    ((image.flatMap encII)[a.toNat]?).getD 0 else callMem.b a }

open FnptrProben in
/-- The certificate and every simulation premise are inhabited together on a
    loaded accepted body; this is not merely a syntactic certificate fixture. -/
theorem block_sound_zeuge :
    CountedReach 3 callLayout 4096 4 256 [] ⟨0, 4096⟩ memory
      48 world (Env.nil : Env FnptrProben.D []) 0 := by
  have lower : lowB 2 addresses callLayout 4 ([], 6) [] (0, 0)
      (body (vertragVon FnptrProben.D 2)) = some (image, 6) := by decide +kernel
  have code : CodeAt memory 0 image := by
    have h : ∀ k : Fin image.length,
        (memory.rd8 (BitVec.ofNat 64 (16 * k.val)) = some (BitVec.ofNat 8 image[k.val].o)) ∧
        memory.rd32 (BitVec.ofNat 64 (16 * k.val) + 4) = some (II.f image[k.val].a) ∧
        memory.rd32 (BitVec.ofNat 64 (16 * k.val) + 8) = some (II.f image[k.val].b) ∧
        memory.rd32 (BitVec.ofNat 64 (16 * k.val) + 12) = some (II.f image[k.val].c) := by
      apply allFin; decide +kernel
    intro k hk
    obtain ⟨op, a, b, c⟩ := h ⟨k, hk⟩
    exact ⟨by simpa using op, by simpa using a, by simpa using b, by simpa using c⟩
  have pre : PreS callLayout memory 0 4096 256 4 image (Env.nil : Env FnptrProben.D []) := by
    refine ⟨by decide, by decide, ?_, code, ?_, ?_, trivial, wstab_true _ _⟩
    · exact ⟨by decide, fun _ _ => rfl, fun _ _ => rfl⟩
    · unfold CodeFar; decide +kernel
    · intro _ x; nomatch x
  have hw : WeltAt memory callLayout world := by
    refine ⟨(fun t => nomatch t), (fun g => ⟨64, ?_, rfl⟩), (fun _ _ _ => rfl)⟩
    cases g
    decide +kernel
  obtain ⟨cert⟩ := block_certificate_zeuge (L := callLayout) (reserved := 0)
    (vertragVon FnptrProben.D 2) world
  exact cert.sound lower (by decide) call_win (by decide)
    (by intro j hj; cases hj) pre hw
end BlockCostProbe

end Gabbro.Stage0.Senke
