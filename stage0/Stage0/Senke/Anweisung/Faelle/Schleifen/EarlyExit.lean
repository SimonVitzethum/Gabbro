/- Executable checks of actual lowered early exits, with exact Runner step counts. -/
import Stage0.Senke.Anweisung.Faelle.Schleifen.CounterRun
import Stage0.Senke.Anweisung.Faelle.Schleifen.CountedLoop
import Stage0.Senke.Anweisung.Faelle.Schleifen.StatementCost

namespace Gabbro.Stage0.Senke.EarlyExitProbe
open Gabbro.Grammatik Runner Runner.Mem Runner.IR CounterCallProbe FnptrProben
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- Interpret only the existing Runner memory requests; system calls remain refused. -/
def answer : Runner.Res T → Mem → Option (T × Mem)
  | .next t, m => some (t, m)
  | .ask o k, m => do
    let (a, m') ← memAns m o
    answer (k a) m'
  | _, _ => none

theorem answer_sound [Kern] {r : Runner.Res T} {m m' : Mem} {t : T}
    (h : answer r m = some (t, m')) : Run r m t m' := by
  induction r generalizing m with
  | next s => cases h; exact .next
  | fault => cases h
  | unk => cases h
  | ask o k ih =>
    simp only [answer] at h
    cases hm : memAns m o with
    | none => simp [hm] at h
    | some p =>
      obtain ⟨a, m1⟩ := p
      exact .ask hm (ih a (by simpa [hm] using h))

/-- Exactly n instructions, each fetched by Runner.step, including jumps. -/
def execute : Nat → T → Mem → Option (T × Mem)
  | 0, t, m => some (t, m)
  | n + 1, t, m => do
    let (t', m') ← answer (step t) m
    execute n t' m'

theorem execute_counted [Kern] (n : Nat) {t t' : T} {m m' : Mem}
    (h : execute n t m = some (t', m')) : Counted n t m t' m' := by
  induction n generalizing t m with
  | zero => cases h; exact .refl _ _
  | succ n ih =>
    simp only [execute] at h
    cases hm : answer (step t) m with
    | none => simp [hm] at h
    | some p =>
      obtain ⟨s, m1⟩ := p
      exact .next (answer_sound hm) (ih (by simpa [hm] using h))

/-- Erase the independently checked instruction count for qualitative simulation. -/
theorem execute_sound [Kern] (n : Nat) {t t' : T} {m m' : Mem}
    (h : execute n t m = some (t', m')) : Star t m t' m' :=
  (execute_counted n h).forget

/-- Return uses a scratch/result area above the sentinel and reserved counter. -/
def exitBody (kind : Fin 3) : Block D (vertragVon D 2) true [] [] [] :=
  .cons (match kind.val with
    | 0 => .next rfl
    | 1 => .leave rfl
    | _ => .ret (.val (.widen (by decide) (by decide) (.lit 43))) (.refl [])) .nil

def lowered (kind : Fin 3) :=
  lowB (reserved := 8) 1 addresses callLayout 4 ([ci 1 5 1 0], 6)
    [6, 7] (128, -48) (exitBody kind)
def code (kind : Fin 3) := ((lowered kind).getD ([], 0)).1

def memory (kind : Fin 3) : Mem :=
  let base : Mem := ⟨fun _ => 0, fun _ => true, fun _ => true⟩
  let m := write (write (write (write base 4096 8 3000) 4104 8 5000)
    (slot 4096 6) 8 2) (slot 4096 7) 8 77
  { m with b := fun a => if 2048 ≤ a.toNat ∧ a.toNat < 2048 + 16 * (code kind).length
      then (((code kind).flatMap encII)[a.toNat - 2048]?).getD 0 else m.b a }

def cost (kind : Fin 3) : Nat := if kind.val < 2 then 1 else 6

def observed (kind : Fin 3) : Option (Runner.W × Runner.W × Option Runner.W × Option Runner.W × Option Runner.W) := do
  let (t, m) ← execute (cost kind) ⟨2048, 4096⟩ (memory kind)
  pure (t.pc, t.fp, m.rd64 (slot 4096 2), m.rd64 (slot 4096 6), m.rd64 (slot 4096 7))

/-- Both jumps have one emitted instruction. Return executes its value, copy,
    ensures, branch, result copy and return; the failure tail is not executed. -/
theorem actual_exit_zeuge :
    (lowered 0).isSome = true ∧ (lowered 1).isSome = true ∧
    (lowered 2).isSome = true ∧
    (code 0).length = 1 ∧ (code 1).length = 1 ∧
    observed 0 = some (2016, 4096, some 0, some 2, some 77) ∧
    observed 1 = some (2192, 4096, some 0, some 2, some 77) ∧
    observed 2 = some (3000, 5000, some 43, some 2, some 77) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals decide +kernel

/-- Cost is derived from emitted instruction lists, excluding only the
    untaken contract-failure tail of return. No smaller prefix reaches the
    destination. The evaluator counts fetched instructions, not memory requests. -/
theorem exact_cost_zeuge :
    cost 0 = (code 0).length ∧ cost 1 = (code 1).length ∧
    cost 2 + (stopC 102 5).length = (code 2).length ∧
    (List.finRange 3).all (fun kind =>
      (List.range (cost kind)).all (fun n =>
        match execute n ⟨2048, 4096⟩ (memory kind) with
        | some (t, _) => t.pc != (if kind.val = 0 then 2016 else if kind.val = 1 then 2192 else 3000)
        | none => false)) = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- The accepted next/leave/return images carry exact 1/1/6 instruction
    counts and all observed ABI and sentinel facts at the same endpoint. -/
theorem actual_runner_zeuge [Kern] (kind : Fin 3) :
    ∃ t m, Counted (cost kind) ⟨2048, 4096⟩ (memory kind) t m ∧
      t.pc = (if kind.val = 0 then 2016 else if kind.val = 1 then 2192 else 3000) ∧
      t.fp = (if kind.val < 2 then 4096 else 5000) ∧
      m.rd64 (slot 4096 2) = some (if kind.val < 2 then 0 else 43) ∧
      m.rd64 (slot 4096 6) = some 2 ∧ m.rd64 (slot 4096 7) = some 77 := by
  have computed : ∀ k : Fin 3,
      (match execute (cost k) ⟨2048, 4096⟩ (memory k) with
      | none => false
      | some (t, m) =>
        t.pc == (if k.val = 0 then 2016 else if k.val = 1 then 2192 else 3000) &&
        t.fp == (if k.val < 2 then 4096 else 5000) &&
        m.rd64 (slot 4096 2) == some (if k.val < 2 then 0 else 43) &&
        m.rd64 (slot 4096 6) == some 2 && m.rd64 (slot 4096 7) == some 77) = true := by
    apply allFin
    decide +kernel
  have hc := computed kind
  cases he : execute (cost kind) ⟨2048, 4096⟩ (memory kind) with
  | none => simp only [he] at hc; cases hc
  | some p =>
    obtain ⟨t, m⟩ := p
    simp only [he, Bool.and_eq_true, beq_iff_eq] at hc
    exact ⟨t, m, execute_counted (cost kind) he, hc.1.1.1.1,
      hc.1.1.1.2, hc.1.1.2, hc.1.2, hc.2⟩

local instance (m : Mem) (pc : W) (o : Nat) (a b c : BitVec 32) :
    Decidable (InsAt m pc o a b c) :=
  if h : m.rd8 pc = some (BitVec.ofNat 8 o) ∧ m.rd32 (pc + 4) = some a ∧
      m.rd32 (pc + 8) = some b ∧ m.rd32 (pc + 12) = some c then
    .isTrue ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  else .isFalse (fun h' => h ⟨h'.op, h'.f1, h'.f2, h'.f3⟩)

/-- Actual source loop used to jointly exercise the terminal-pass premises.
    The generic theorem is instantiated on the accepted image, not a substitute
    empty loop. Its body leaves on the first pass. -/
def leaveLoop : Stmt D (vertragVon D 2) false [] [] [] :=
  .forever () .tru (.cons (.leave rfl) .nil)

def leaveImage : List II := foreverCode 4 5 6 1 [ci 1 6 1 0] [ci 18 144 0 0]

theorem leave_lowering_zeuge :
    lowS (reserved := 2) 1 addresses callLayout 4 ([], 6) [] (0, 0)
      leaveLoop = some (leaveImage, 14) := by decide +kernel

def leaveMemory : Mem := {
  b := fun a => if a.toNat < 16 * leaveImage.length then
    ((leaveImage.flatMap encII)[a.toNat]?).getD 0
    else if a = slot 1024 4 ∨ a = slot 1024 5 then 1 else 0
  rd := fun _ => true
  wr := fun _ => true }

def leaveDecremented := write leaveMemory (slot 1024 4) 8 0
def leaveResult := write leaveDecremented (slot 1024 6) 8 1

/-- All quantified premises of the early-exit induction hold together on
    a loaded, nonempty accepted source body. The five instructions are the
    counter test, decrement, invariant, branch, and leave. -/
theorem counted_counter_loop_exits_zeuge [Kern] :
    ∃ u b nb, nb ≤ 7 ∧ Counted nb ⟨32, 1024⟩ leaveMemory u b ∧
      u = ⟨240, 1024⟩ := by
  let I : Nat → Mem → Prop := fun n m => n = 1 ∧ m = leaveMemory
  have result := counted_counter_loop_exits I (fun u _ => u = ⟨240, 1024⟩)
    32 1024 176 4 5 160 3
    (by rintro n m ⟨rfl, rfl⟩; decide +kernel)
    (by rintro n m ⟨rfl, rfl⟩; decide +kernel)
    (by rintro n m ⟨h, rfl⟩; decide +kernel)
    (by rintro n m ⟨rfl, rfl⟩; decide +kernel)
    (by
      rintro n m ⟨hn, rfl⟩ fits
      have hn0 : n = 0 := by omega
      subst n
      refine ⟨leaveDecremented, leaveResult, 3, ?_, by decide, Or.inr (Or.inr ?_)⟩
      · rfl
      · exact ⟨⟨240, 1024⟩, execute_counted 3 (by rfl), rfl⟩)
    (by decide) (by decide : 1 < 2 ^ 64) (by exact ⟨rfl, rfl⟩)
  obtain ⟨u, b, nb, bound, run, done⟩ := result
  refine ⟨u, b, nb, bound, run, ?_⟩
  rcases done with ⟨_, impossible, _⟩ | done
  · contradiction
  · exact done

end Gabbro.Stage0.Senke.EarlyExitProbe

namespace Gabbro.Stage0.Senke.LoopJumpCostProbe
open Gabbro.Grammatik Runner Runner.IR Runner.Mem FnptrProben
set_option maxHeartbeats 2000000
variable [Kern]
def body (next : Bool) : Block D (vertragVon D 2) true [] [] [] :=
  .cons (if next then .next rfl else .leave rfl) .nil
def image (next : Bool) : List II := [ci 18 (if next then -32 else 144) 0 0]
def memory (next : Bool) : Mem :=
  { callMem with b := fun a => if 2048 ≤ a.toNat ∧ a.toNat < 2064 then
      (((image next).flatMap encII)[a.toNat - 2048]?).getD 0 else callMem.b a }
theorem loopJumpBlock_counted_zeuge (next : Bool) :
    lowB (reserved := 8) 1 addresses callLayout 4 ([], 6) [6, 7]
      (128, -48) (body next) = some (image next, 12) ∧
    CountedReach 1 callLayout 4096 4 256 [6, 7] ⟨2048, 4096⟩ (memory next)
      (if next then 2016 else 2192) world (Env.nil : Env D []) 8 := by
  have lower : lowB (reserved := 8) 1 addresses callLayout 4 ([], 6) [6, 7]
      (128, -48) (body next) = some (image next, 12) := by
    cases next <;> decide +kernel
  have pre : PreS callLayout (memory next) 2048 4096 256 12
      (image next) (Env.nil : Env D []) 8 := by
    refine ⟨by decide, by decide, ⟨by decide, fun _ _ => rfl, fun _ _ => rfl⟩,
      ?_, ?_, (fun _ x => nomatch x), trivial, wstab_true _ _⟩
    · intro k hk
      have : k = 0 := by simpa [image] using hk
      subst k
      cases next <;> simp only [image, Bool.false_eq_true, ↓reduceIte,
        List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero, ci]
      all_goals exact ⟨by decide +kernel, by decide +kernel,
        by decide +kernel, by decide +kernel⟩
    · cases next <;> unfold CodeFar image <;> decide +kernel
  have hw : WeltAt (memory next) callLayout world := by
    refine ⟨(fun t => nomatch t), (fun g => ⟨64, ?_, rfl⟩), (fun _ _ _ => rfl)⟩
    cases g
    cases next <;> decide +kernel
  refine ⟨lower, ?_⟩
  have result := loopJumpBlock_counted next lower pre hw
  cases next <;> exact result
/-- The accepted source jumps inhabit the canonical outcome index jointly with
    their exact cost, world, environment and enclosing protected counters. -/
theorem countedSim_loopJump_zeuge (P : Programm D) (σ0 : World D)
    (ρ0 : Env D (D.params 2)) (next : Bool) :
    CountedSim 1 callLayout P 2 σ0 ρ0 3000 5000 4096 4 256 [6, 7]
      ⟨2048, 4096⟩ (memory next) 2064 2192 2016
      (if next then .next rfl world (Env.nil : Env D [])
       else .leave rfl world (Env.nil : Env D [])) 8 := by
  have h := (loopJumpBlock_counted_zeuge next).2
  cases next <;> exact h

/-- The canonical child certificate retains the actual abrupt source outcome. -/
theorem recursiveBlockCost_jump_zeuge (P : Programm D) (C : D.Fn → List II)
    (next : Bool) :
    Nonempty (recursiveBlockCost callLayout 8 P 1 addresses C 1 128
      (vertragVon D 2) true (body next) world (Env.nil : Env D [])
      (if next then .next rfl world Env.nil else .leave rfl world Env.nil) 1) ∧
    lowB (reserved := 8) 1 addresses callLayout 4 ([], 6) [6, 7]
      (128, -48) (body next) = some (image next, 12) := by
  exact ⟨⟨.jump rfl next⟩, (loopJumpBlock_counted_zeuge next).1⟩

end Gabbro.Stage0.Senke.LoopJumpCostProbe

namespace Gabbro.Stage0.Senke.ForeverPassCostProbe
open Gabbro.Grammatik Runner Runner.IR Runner.Mem FnptrProben
variable [Kern]
set_option maxHeartbeats 2000000
local instance (m : Mem) (pc : W) (o : Nat) (a b c : BitVec 32) :
    Decidable (InsAt m pc o a b c) :=
  if h : m.rd8 pc = some (BitVec.ofNat 8 o) ∧ m.rd32 (pc + 4) = some a ∧
      m.rd32 (pc + 8) = some b ∧ m.rd32 (pc + 12) = some c then
    .isTrue ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  else .isFalse (fun h' => h ⟨h'.op, h'.f1, h'.f2, h'.f3⟩)
def image (positive : Bool) : List II :=
  [ci 1 12 (if positive then 1 else 0) 0, ci 19 12 48 0,
    ci 18 80 0 0, ci 18 64 0 0] ++ stopC 104 12
def memory (positive : Bool) : Mem :=
  { callMem with b := fun a => if 2048 ≤ a.toNat ∧ a.toNat < 2160 then
      (((image positive).flatMap encII)[a.toNat - 2048]?).getD 0 else callMem.b a }
theorem joint (positive : Bool) :
    PreS callLayout (memory positive) 2048 4096 256 12 (image positive)
      (Env.nil : Env D []) 8 ∧
    WIn callLayout 4096 128 256 ∧
    WeltAt (memory positive) callLayout world ∧
    Umf callLayout addresses (fun _ => []) 2 (memory positive) 4096 128 256 := by
  have frame : FrameOK (memory positive) 4096 256 :=
    ⟨by decide, fun _ _ => rfl, fun _ _ => rfl⟩
  have code : CodeAt (memory positive) 2048 (image positive) := by
    have h : ∀ k : Fin (image positive).length,
        InsAt (memory positive) (2048 + BitVec.ofNat 64 (16 * k.val))
          (image positive)[k.val].o (II.f (image positive)[k.val].a)
          (II.f (image positive)[k.val].b) (II.f (image positive)[k.val].c) := by
      cases positive <;> apply allFin <;> decide +kernel
    exact fun k hk => h ⟨k, hk⟩
  have pre : PreS callLayout (memory positive) 2048 4096 256 12 (image positive)
      (Env.nil : Env D []) 8 :=
    ⟨by decide, by decide, frame, code, by cases positive <;> unfold CodeFar image stopC sysC <;> decide +kernel,
      (fun _ x => nomatch x), trivial, wstab_true _ _⟩
  have inside : WIn callLayout 4096 128 256 := by
    refine ⟨⟨(fun t => nomatch t), fun _ => ⟨by change 8192 ≤ 8192; decide, by change 8192 + 8 ≤ 8200; decide⟩, by decide⟩,
      ?_, by decide, by decide, by decide⟩
    constructor
    · intro c c' hc hc' h
      cases c with
      | elem t => nomatch t
      | glob g => cases c' with
        | elem t => nomatch t
        | glob g' => cases g; cases g'; rfl
    · intro c hc
      cases c with
      | elem t => nomatch t
      | glob _ => rfl
  have hw : WeltAt (memory positive) callLayout world := by
    refine ⟨(fun t => nomatch t), (fun g => ⟨64, ?_, rfl⟩), (fun _ _ _ => rfl)⟩
    cases g
    cases positive <;> decide +kernel
  have sync : SyncOK (memory positive) callLayout 4096 128 :=
    ⟨by decide, by decide, by decide, by decide, by decide, by decide,
      (fun l => nomatch l), by decide, (fun l => nomatch l),
      (fun l => nomatch l), (fun l => nomatch l)⟩
  refine ⟨pre, inside, hw, ?_⟩
  refine ⟨?_, ?_, by decide, sync, by decide⟩
  · intro f
    have far : ∀ f : Fin 3, CodeFar (BitVec.ofNat 64 (addresses f)) 0 4096 256 := by
      unfold CodeFar
      apply allFin
      decide +kernel
    exact ⟨fun k hk => by simp at hk, far f⟩
  · cases positive <;> decide +kernel

/-- Accepted nonempty next/leave source bodies jointly inhabit the positive
    invariant composition, including the two protected outer counter slots. -/
theorem forever_positive_counted_zeuge (P : Programm D) (σ0 : World D)
    (ρ0 : Env D (D.params 2)) (next : Bool) :
    CountedSim 3 callLayout P 2 σ0 ρ0 3000 5000 4096 4 256 [6, 7]
      ⟨2048, 4096⟩ (memory true) 2096 2160 2160
      (if next then .next rfl world (Env.nil : Env D [])
       else .leave rfl world (Env.nil : Env D [])) 8 := by
  obtain ⟨pre, inside, hw, around⟩ := joint true
  have lower : lowB (reserved := 8) 1 addresses callLayout 4 ([], 6) [6, 7]
      (exPlus (0, 0) 4) (LoopJumpCostProbe.body next) = some ([ci 18 80 0 0], 12) := by
    cases next <;> decide +kernel
  apply forever_positive_counted (inv := .tru) (ni := 1) (nb := 1)
    (body := LoopJumpCostProbe.body next) (ex := (0, 0))
    (A := addresses) (C := fun _ => []) (dv := 2)
    (invariant := ExprCost.truth) (lowerInv := by rfl) (lowerBody := lower)
    (fitsInv := by decide) (inside := inside) (abi := by decide)
    (low := by decide) (hprotected := by intro j hj; simp at hj; unfold frei FB; omega)
    (pre := pre) (surroundings := around) (world := hw)
  intro m1 hp hu hw1
  have result := loopJumpBlock_counted next lower hp hw1
  cases next <;> exact result

/-- A source false invariant reaches the pending failure syscall in four
    instructions, while its nonempty source body remains unexecuted. -/
theorem forever_false_stop_counted_zeuge (P : Programm D) :
    CountedStops 4 ⟨2048, 4096⟩ (memory false) 104 := by
  obtain ⟨pre, inside, hw, around⟩ := joint false
  exact forever_false_stop_counted (reserved := 8) (cc := [ci 1 12 0 0])
    (cb := [ci 18 80 0 0]) (tb := 12) (inv := .fls) (body := LoopJumpCostProbe.body true)
    (ni := 1) (P := P) (passes := 1) (σ' := world) (ρ' := Env.nil) (A := addresses) (C := fun _ => [])
    (dv := 2) (lo := 4) (ens := ([], 6)) (pr := [6, 7]) (ex := (0, 0))
    (invariant := ExprCost.falsity) (lowerInv := by rfl) (lowerBody := by decide +kernel)
    (jumpFits := by decide) (stopRoom := by decide) (fitsInv := by decide)
    (fitsBody := by decide) (inside := inside) (low := by decide)
    (hprotected := by intro j hj; simp at hj; unfold frei FB; omega)
    (pre := pre) (surroundings := around) (world := hw)
end Gabbro.Stage0.Senke.ForeverPassCostProbe


namespace Gabbro.Stage0.Senke.SourceStopProbe
open Gabbro.Grammatik Runner Runner.IR Runner.Mem
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
variable {D : Deklaration}
def source (V : Vertrag D) (assumption : D.Annahme) : Block D V false [] [] [] :=
  .cons (.forever assumption .tru (.cons (.leave rfl) .nil)) .nil

theorem sourceStop_zeuge [Kern] (L : Lay D) (P : Programm D) (A : D.Fn → Nat)
    (C : D.Fn → List II) (V : Vertrag D) (assumption : D.Annahme) (σ : World D) :
    Nonempty (recursiveBlockCost L 2 P 0 A C 0 32 V false
      (source V assumption) σ Env.nil (.hardware (.fortschritt assumption)) 5) := by
  unfold source
  refine ⟨recursiveBlockCost.sourceStop (inv := .tru) (body := .cons (.leave rfl) .nil) (rest := .nil) rfl ?_⟩
  intro lo ens pr ex code top lower
  dsimp only [lowS] at lower
  split at lower
  · rw [show lowE L (Expr.tru (Γ := []) (Λ := [])) (frei [] 2) 2 =
        some ([ci 1 6 1 0], 7) from rfl] at lower
    simp only [Bind.bind, Option.bind_some] at lower
    obtain ⟨cb, tb, lowered, rfl, _⟩ := foreverC_actual lower
    change some ([ci 18 144 0 0], 6) = some (cb, tb) at lowered
    have pair := Option.some.inj lowered
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj pair
    simp [foreverCode_length]
  · simp at lower
end Gabbro.Stage0.Senke.SourceStopProbe

namespace Gabbro.Stage0.Senke.PositiveHeaderProbe
open Gabbro.Grammatik Runner Runner.IR Runner.Mem FnptrProben
variable [Kern]
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
local instance (m : Mem) (pc : W) (o : Nat) (a b c : BitVec 32) :
    Decidable (InsAt m pc o a b c) :=
  if h : m.rd8 pc = some (BitVec.ofNat 8 o) ∧ m.rd32 (pc + 4) = some a ∧
      m.rd32 (pc + 8) = some b ∧ m.rd32 (pc + 12) = some c then
    .isTrue ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  else .isFalse (fun h' => h ⟨h'.op, h'.f1, h'.f2, h'.f3⟩)
def image : List II := foreverCounter 6 7 128

def memory : Mem :=
  let base := write (write callMem (slot 4096 6) 8 2) (slot 4096 7) 8 1
  { base with b := fun a => if 2048 ≤ a.toNat ∧ a.toNat < 2080 then
      ((image.flatMap encII)[a.toNat - 2048]?).getD 0 else base.b a }

/-- All header premises hold jointly on a real nonzero counter image. -/
theorem counter_positive_source_counted_zeuge :
    ∃ m', Counted 2 ⟨2048, 4096⟩ memory ⟨2080, 4096⟩ m' ∧
      PreS callLayout m' 2080 4096 256 8 [] (Env.nil : Env D []) 4 ∧
      WeltAt m' callLayout world ∧ Agree 4096 6 256 memory m' ∧
      m'.rd64 (slot 4096 6) = some 1 ∧
      m'.rd64 (slot 4096 7) = some 1 := by
  have frame : FrameOK memory 4096 256 :=
    ⟨by decide, fun _ _ => rfl, fun _ _ => rfl⟩
  have code : CodeAt memory 2048 image := by
    have h : ∀ k : Fin image.length,
        InsAt memory (2048 + BitVec.ofNat 64 (16 * k.val))
          image[k.val].o (II.f image[k.val].a) (II.f image[k.val].b) (II.f image[k.val].c) := by
      apply allFin
      decide +kernel
    exact fun k hk => h ⟨k, hk⟩
  have pre : PreS callLayout memory 2048 4096 256 8
      (foreverCounter 6 7 128 ++ []) (Env.nil : Env D []) 4 :=
    ⟨by decide, by decide, frame, by simpa [image] using code,
      by unfold CodeFar foreverCounter; decide +kernel,
      (fun _ x => nomatch x), trivial, wstab_true _ _⟩
  have hw : WeltAt memory callLayout world := by
    refine ⟨(fun t => nomatch t), (fun g => ⟨64, ?_, rfl⟩), (fun _ _ _ => rfl)⟩
    cases g
    decide +kernel
  exact counter_positive_source_counted (L := callLayout) (fuel := 2)
    (Γ := []) (reserved := 4) (counter := 6) (one := 7)
    (pc := 2048) (fp := 4096) (code := []) (jump := 128)
    (ForeverPassCostProbe.joint true).2.1 pre hw
    (by decide) (by decide) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide)
end Gabbro.Stage0.Senke.PositiveHeaderProbe

namespace Gabbro.Stage0.Senke.InitializedPassProbe
open Gabbro.Grammatik Runner Runner.IR Runner.Mem FnptrProben
variable [Kern]
set_option maxHeartbeats 2000000
local instance (m : Mem) (pc : W) (o : Nat) (a b c : BitVec 32) :
    Decidable (InsAt m pc o a b c) :=
  if h : m.rd8 pc = some (BitVec.ofNat 8 o) ∧ m.rd32 (pc + 4) = some a ∧
      m.rd32 (pc + 8) = some b ∧ m.rd32 (pc + 12) = some c then
    .isTrue ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  else .isFalse (fun h' => h ⟨h'.op, h'.f1, h'.f2, h'.f3⟩)
def image (positive : Bool) : List II :=
  [ci 1 8 2 0, ci 1 9 1 0] ++ foreverCounter 8 9 0 ++ [ci 1 12 (if positive then 1 else 0) 0, ci 19 12 48 0,
    ci 18 80 0 0, ci 18 64 0 0] ++ stopC 104 12
def memory (positive : Bool) : Mem :=
  { callMem with b := fun a => if 2048 ≤ a.toNat ∧ a.toNat < 2224 then
      (((image positive).flatMap encII)[a.toNat - 2048]?).getD 0 else callMem.b a }
theorem joint (positive : Bool) :
    PreS callLayout (memory positive) 2048 4096 256 12 (image positive)
      (Env.nil : Env D []) 8 ∧
    WIn callLayout 4096 128 256 ∧
    WeltAt (memory positive) callLayout world ∧
    Umf callLayout addresses (fun _ => []) 2 (memory positive) 4096 128 256 := by
  have frame : FrameOK (memory positive) 4096 256 :=
    ⟨by decide, fun _ _ => rfl, fun _ _ => rfl⟩
  have code : CodeAt (memory positive) 2048 (image positive) := by
    have h : ∀ k : Fin (image positive).length,
        InsAt (memory positive) (2048 + BitVec.ofNat 64 (16 * k.val))
          (image positive)[k.val].o (II.f (image positive)[k.val].a)
          (II.f (image positive)[k.val].b) (II.f (image positive)[k.val].c) := by
      cases positive <;> apply allFin <;> decide +kernel
    exact fun k hk => h ⟨k, hk⟩
  have pre : PreS callLayout (memory positive) 2048 4096 256 12 (image positive)
      (Env.nil : Env D []) 8 :=
    ⟨by decide, by decide, frame, code, by cases positive <;> unfold CodeFar image stopC sysC <;> decide +kernel,
      (fun _ x => nomatch x), trivial, wstab_true _ _⟩
  have inside : WIn callLayout 4096 128 256 := by
    refine ⟨⟨(fun t => nomatch t), fun _ => ⟨by change 8192 ≤ 8192; decide, by change 8192 + 8 ≤ 8200; decide⟩, by decide⟩,
      ?_, by decide, by decide, by decide⟩
    constructor
    · intro c c' hc hc' h
      cases c with
      | elem t => nomatch t
      | glob g => cases c' with
        | elem t => nomatch t
        | glob g' => cases g; cases g'; rfl
    · intro c hc
      cases c with
      | elem t => nomatch t
      | glob _ => rfl
  have hw : WeltAt (memory positive) callLayout world := by
    refine ⟨(fun t => nomatch t), (fun g => ⟨64, ?_, rfl⟩), (fun _ _ _ => rfl)⟩
    cases g
    cases positive <;> decide +kernel
  have sync : SyncOK (memory positive) callLayout 4096 128 :=
    ⟨by decide, by decide, by decide, by decide, by decide, by decide,
      (fun l => nomatch l), by decide, (fun l => nomatch l),
      (fun l => nomatch l), (fun l => nomatch l)⟩
  refine ⟨pre, inside, hw, ?_⟩
  refine ⟨?_, ?_, by decide, sync, by decide⟩
  · intro f
    have far : ∀ f : Fin 3, CodeFar (BitVec.ofNat 64 (addresses f)) 0 4096 256 := by
      unfold CodeFar
      apply allFin
      decide +kernel
    exact ⟨fun k hk => by simp at hk, far f⟩
  · cases positive <;> decide +kernel

theorem initialized_positive_source_counted_zeuge (P : Programm D) (σ0 : World D)
    (ρ0 : Env D (D.params 2)) (next : Bool) :
    ∃ n, n ≤ 7 ∧ CountedSim n callLayout P 2 σ0 ρ0 3000 5000 4096 4 256 [6, 7]
      ⟨2048, 4096⟩ (memory true) 2160 2224 2224
      (if next then .next rfl world (Env.nil : Env D [])
       else .leave rfl world (Env.nil : Env D [])) 8 := by
  obtain ⟨pre, inside, hw, around⟩ := joint true
  have lower : lowB (reserved := 8) 1 addresses callLayout 4 ([], 6) [6, 7]
      (exPlus (0, 0) 4) (LoopJumpCostProbe.body next) = some ([ci 18 80 0 0], 12) := by
    cases next <;> decide +kernel
  exact recursiveBlockCost.initialized_positive_source_counted
    (inv := .tru) (ni := 1) (nb := 1) (body := LoopJumpCostProbe.body next)
    (counter := 8) (one := 9) (value := 2) (jump := 0)
    (ex := (0, 0)) (A := addresses) (C := fun _ => []) (dv := 2)
    ExprCost.truth rfl lower (by decide) inside (by decide) (by decide)
    (by intro j hj; simp at hj; unfold frei FB; omega) pre around hw
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by intro j hj; simp at hj; omega) (by decide) (by decide)
    (.jump rfl next) (by decide) (by decide) (by decide) (by decide)
end Gabbro.Stage0.Senke.InitializedPassProbe
