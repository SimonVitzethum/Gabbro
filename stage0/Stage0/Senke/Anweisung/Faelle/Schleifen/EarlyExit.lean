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
end Gabbro.Stage0.Senke.LoopJumpCostProbe
