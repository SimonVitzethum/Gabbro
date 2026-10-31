/- A real world store and call preserve a live sentinel in a nonzero reserved frame. -/
import Stage0.Senke.Ausdruck.FnptrAufrufProben
import Stage0.Senke.Anweisung.Faelle.Schleifen.Runtime

namespace Gabbro.Stage0.Senke.ReservedCallProbe
open Gabbro.Grammatik Runner.IR Runner.Mem FnptrProben
set_option maxRecDepth 100000

/-- A real world store followed by an actual call, sharing a reserved caller frame. -/
def body : Block D (vertragVon D 2) false [] [] [] :=
  .cons (.assignGlob () pointer rfl (by intro w h; cases h))
    (.cons (.call 0 .nil (fit 2) rfl) .nil)

def lowered := lowB (reserved := 4) 1 addresses callLayout 4 ([ci 1 5 1 0], 6) [4] (0, 0) body
def code : List II := (lowered.getD ([], 0)).1
def top : Nat := (lowered.getD ([], 0)).2

def image : List II := [ci 1 6 2 0] ++ code ++ [ci 18 (-(16 * (code.length : Int))) 0 0]

def memory : Runner.Mem := { callMem with
  b := fun a => if 2032 ≤ a.toNat ∧ a.toNat < 2032 + 16 * image.length then
      ((image.flatMap encII)[a.toNat - 2032]?).getD 0 else if a.toNat = 4128 then 77 else callMem.b a }

theorem lowering : lowB (reserved := 4) 1 addresses callLayout 4 ([ci 1 5 1 0], 6) [4] (0, 0) body = some (code, top) := by
  decide +kernel

local instance (m : Runner.Mem) (pc : Runner.W) (o : Nat) (a b c : BitVec 32) :
    Decidable (InsAt m pc o a b c) :=
  if h : m.rd8 pc = some (BitVec.ofNat 8 o) ∧ m.rd32 (pc + 4) = some a ∧
      m.rd32 (pc + 8) = some b ∧ m.rd32 (pc + 12) = some c then
    .isTrue ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  else .isFalse (fun h' => h ⟨h'.op, h'.f1, h'.f2, h'.f3⟩)

theorem code_at : CodeAt memory 2048 code := by
  have h : ∀ k : Fin code.length, InsAt memory (2048 + BitVec.ofNat 64 (16 * k.val))
      code[k.val].o (II.f code[k.val].a) (II.f code[k.val].b) (II.f code[k.val].c) := by
    apply allFin
    decide +kernel
  exact fun k hk => h ⟨k, hk⟩

theorem functions_at : PCode memory addresses target 4096 256 := by
  have h : (List.finRange 3).all (fun f => (List.finRange (target f).length).all (fun k =>
      decide (InsAt memory (BitVec.ofNat 64 (addresses f) + BitVec.ofNat 64 (16 * k.val))
        (target f)[k.val].o (II.f (target f)[k.val].a) (II.f (target f)[k.val].b) (II.f (target f)[k.val].c)))) = true := by
    decide +kernel
  change ∀ f : Fin 3, CodeAt memory (BitVec.ofNat 64 (addresses f)) (target f) ∧
    CodeFar (BitVec.ofNat 64 (addresses f)) (target f).length 4096 256
  refine fun f => ⟨fun k hk => ?_, (targets_code f).2⟩
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp h f (by simp)) ⟨k, hk⟩ (by simp))

theorem frame : FrameOK memory 4096 256 := ⟨by decide, fun _ _ => rfl, fun _ _ => rfl⟩

theorem pre [Kern] : PreS callLayout memory 2048 4096 256 8 code (Env.nil : Env D []) 4 := by
  refine ⟨by decide, by decide, frame, code_at, ?_, (fun _ x => nomatch x), trivial, wstab_true _ _⟩
  unfold CodeFar
  decide +kernel

theorem world_at : WeltAt memory callLayout world := by
  refine ⟨(fun t => nomatch t), (fun g => ⟨64, ?_, rfl⟩), (fun _ _ _ => rfl)⟩
  cases g
  decide +kernel

theorem sync : SyncOK memory callLayout 4096 128 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide,
    (fun l => nomatch l), by decide, (fun l => nomatch l), (fun l => nomatch l), (fun l => nomatch l)⟩

theorem surroundings [Kern] : Umf callLayout addresses target 2 memory 4096 128 256 :=
  ⟨functions_at, by decide +kernel, by decide, sync, by decide⟩

theorem head : Kopf callLayout 2 memory 4096 256 0 0 (Env.nil : Env D []) tiny world :=
  ⟨by decide +kernel, by decide +kernel, (fun _ x => nomatch x), by decide, fun _ h => nomatch h⟩

/-- Initialization in front of the real source-derived store/call body preserves
    both enclosing sentinels and reconstructs its full entry contract. -/
theorem reserved_literal_entry_zeuge [Kern] :
    ∃ m', Runner.IR.Star ⟨2032, 4096⟩ memory ⟨2048, 4096⟩ m' ∧
      AgreeW callLayout 4096 4 256 memory m' ∧
      PreS callLayout m' 2048 4096 256 8 code (Env.nil : Env D []) 4 ∧
      Umf callLayout addresses target 2 m' 4096 128 256 ∧
      Kopf callLayout 2 m' 4096 256 0 0 (Env.nil : Env D []) tiny world ∧
      WeltAt m' callLayout world ∧ Keeps 4096 [4, 5] memory m' ∧
      m'.rd64 (slot 4096 6) = some 2 := by
  have entry : CodeAt memory 2032 ([ci 1 6 2 0] ++ code) := by
    have h : ∀ k : Fin (1 + code.length),
        InsAt memory (2032 + BitVec.ofNat 64 (16 * k.val))
          (([ci 1 6 2 0] ++ code)[k.val]'(by simp; omega)).o
          (II.f (([ci 1 6 2 0] ++ code)[k.val]'(by simp; omega)).a)
          (II.f (([ci 1 6 2 0] ++ code)[k.val]'(by simp; omega)).b)
          (II.f (([ci 1 6 2 0] ++ code)[k.val]'(by simp; omega)).c) := by
      apply allFin
      decide +kernel
    exact fun k hk => h ⟨k, by simpa [Nat.add_comm] using hk⟩
  have hp : PreS callLayout memory 2032 4096 256 8
      ([ci 1 6 2 0] ++ code) (Env.nil : Env D []) 4 := by
    refine ⟨by decide, by decide, frame, entry, ?_,
      (fun _ x => nomatch x), trivial, wstab_true _ _⟩
    unfold CodeFar
    decide +kernel
  exact reserved_literal_entry (lo := 4) (pr := [4, 5]) (cell := 6)
    (reserved := 4) (Γ := []) (value := 2) (code := code)
    call_win hp surroundings head world_at (by decide) (by decide)
    (by decide) (by decide) (by decide)
    (by intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; rcases hj with rfl | rfl <;> decide)

local instance [Kern] : TorOK callLayout O where
  ans a := nomatch a
  puf a := nomatch a
local instance : SichtOK O := ⟨fun _ _ => rfl⟩

/-- The generic block theorem supplies the complete runtime and frame result. -/
theorem body_simulation [Kern] :
    Reach callLayout 4096 4 256 [4] ⟨2048, 4096⟩ memory
      (2048 + BitVec.ofNat 64 (16 * code.length)) world Env.nil 4 := by
  have h := lowB_ok (reserved := 4) (O := O) (passes := 1) (P := tiny) (f := 2)
    (σ0 := world) (ρ0 := Env.nil) (lo := 4) (pr := [4]) (ex := (0, 0))
    call_spec addresses_bound rfl rfl body code top lowering (by decide +kernel)
    (by decide +kernel) call_win memory 2048 world Env.nil pre (by decide) (by decide)
    surroundings head world_at (by intro j hj; simp only [List.mem_singleton] at hj; subst j; decide)
  change Reach callLayout 4096 4 256 [4] ⟨2048, 4096⟩ memory
    (2048 + BitVec.ofNat 64 (16 * code.length)) _ Env.nil 4 at h
  exact h

/-- Reuse the emitted block in the memory produced by a previous pass. -/
theorem body_simulation_at [Kern] {m : Runner.Mem}
    (hp : PreS callLayout m 2048 4096 256 8 code (Env.nil : Env D []) 4)
    (hu : Umf callLayout addresses target 2 m 4096 128 256)
    (hk : Kopf callLayout 2 m 4096 256 0 0 (Env.nil : Env D []) tiny world)
    (hw : WeltAt m callLayout world) :
    Reach callLayout 4096 4 256 [4] ⟨2048, 4096⟩ m
      (2048 + BitVec.ofNat 64 (16 * code.length)) world Env.nil 4 := by
  have h := lowB_ok (reserved := 4) (O := O) (passes := 1) (P := tiny) (f := 2)
    (σ0 := world) (ρ0 := Env.nil) (lo := 4) (pr := [4]) (ex := (0, 0))
    call_spec addresses_bound rfl rfl body code top lowering (by decide +kernel)
    (by decide +kernel) call_win m 2048 world Env.nil hp (by decide) (by decide)
    hu hk hw (by intro j hj; simp only [List.mem_singleton] at hj; subst j; decide)
  exact h

/-- Arbitrarily many executions of the same emitted write/call/backedge image.
    Every subsequent call uses the frame, code and function-head guarantees
    reconstructed from the preceding execution. The live sentinel is 77. -/
theorem write_call_reentry_zeuge [Kern] (n : Nat) :
    ∃ m', Star ⟨2048, 4096⟩ memory ⟨2048, 4096⟩ m' ∧
      AgreeW callLayout 4096 4 256 memory m' ∧
      PreS callLayout m' 2048 4096 256 8 code (Env.nil : Env D []) 4 ∧
      Umf callLayout addresses target 2 m' 4096 128 256 ∧
      Kopf callLayout 2 m' 4096 256 0 0 (Env.nil : Env D []) tiny world ∧
      WeltAt m' callLayout world ∧ Keeps 4096 [4] memory m' ∧
      m'.rd64 (slot 4096 (BitVec.ofNat 64 4)) = some 77 := by
  have edge : InsAt memory (2048 + BitVec.ofNat 64 (16 * code.length)) 18
      (II.f (-(16 * (code.length : Int)))) 0 0 := by decide +kernel
  have far : CodeFar (2048 + BitVec.ofNat 64 (16 * code.length)) 1 4096 256 := by
    unfold CodeFar
    decide +kernel
  induction n with
  | zero => exact ⟨memory, Star.refl _ _, AgreeW.refl _ _ _ _ _, pre,
      surroundings, head, world_at, Keeps.refl _ _ _, by decide +kernel⟩
  | succ n ih =>
    obtain ⟨m, run, frame, hp, hu, hk, hw, kept, sentinel⟩ := ih
    have ec : CodeAt memory (2048 + BitVec.ofNat 64 (16 * code.length))
        [ci 18 (-(16 * (code.length : Int))) 0 0] := by
      intro k h
      have : k = 0 := by simpa using h
      subst k
      simpa [ci, II.f] using edge
    have ec' := codeAt_agreeWIn call_win frame ec far
    have edge' := ec' 0 (by simp)
    simp only [List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at edge'
    obtain ⟨m', step, frame', hp', hu', hk', hw', kept', sentinel'⟩ :=
      Reach.counter_reentry (body_simulation_at hp hu hk hw) call_win hp hu hk
        (counter := 4) (Or.inr (by simp)) (by decide) (by decide) sentinel
        edge' far (by decide +kernel)
    exact ⟨m', run.trans step, frame.trans frame', hp', hu', hk', hw',
      kept.trans kept', sentinel'⟩

/-- All premises hold together; the actual write and callee preserve the live reserved sentinel. -/
theorem write_call_reserved_zeuge [Kern] :
    ∃ m', Star ⟨2048, 4096⟩ memory
      ⟨2048 + BitVec.ofNat 64 (16 * code.length), 4096⟩ m' ∧
      m'.rd64 (slot 4096 (BitVec.ofNat 64 4)) = some 77 := by
  obtain ⟨m', hs, _, _, _, hk⟩ := body_simulation
  refine ⟨m', hs, ?_⟩
  rw [hk 4 (by simp)]
  decide +kernel

/-- The emitted backward jump really returns to the body entry after its store
and reachable call; the live reserved sentinel survives the complete cycle. -/
theorem write_call_backedge_zeuge [Kern] :
    ∃ m', Star ⟨2048, 4096⟩ memory ⟨2048, 4096⟩ m' ∧
      m'.rd64 (slot 4096 (BitVec.ofNat 64 4)) = some 77 := by
  have edge : InsAt memory (2048 + BitVec.ofNat 64 (16 * code.length)) 18
      (II.f (-(16 * (code.length : Int)))) 0 0 := by decide +kernel
  have far : CodeFar (2048 + BitVec.ofNat 64 (16 * code.length)) 1 4096 256 := by
    unfold CodeFar
    decide +kernel
  obtain ⟨m', run, _, _, _, _, kept⟩ := Reach.counter_backedge
    (counter := 4) (value := 77) body_simulation call_win (Or.inr (by simp))
    (by decide) (by decide +kernel) edge far
  refine ⟨m', ?_, kept⟩
  have target : (2048 : Runner.W) + BitVec.ofNat 64 (16 * code.length) +
      sx (II.f (-(16 * (code.length : Int)))) = 2048 := by decide +kernel
  simpa only [target] using run

/-- An actual exit image witnesses the canonical induction's zero and leave
    arms together. This is not a counted write/call-loop witness. -/
def leaveMemory : Runner.Mem := { memory with
  b := fun a => if 2048 ≤ a.toNat ∧ a.toNat < 2096 then
    (((stopC 111 8).flatMap encII)[a.toNat - 2048]?).getD 0 else memory.b a }

theorem forever_runtime_zeuge [Kern] :
    ∀ n : Nat, Sim callLayout tiny 2 world Env.nil 0 0 4096 4 256 [4]
      ⟨2048, 4096⟩ leaveMemory 2048 0 0
      (foreverLauf (l := false) (() : D.Annahme)
        (fun σ ρ => .leave rfl σ ρ) (fun σ ρ => (σ, true)) n world (Env.nil : Env D [])) 4 := by
  have hc : CodeAt leaveMemory 2048 (stopC 111 8) := by
    have h : ∀ k : Fin (stopC 111 8).length,
        InsAt leaveMemory (2048 + BitVec.ofNat 64 (16 * k.val))
          (stopC 111 8)[k.val].o (II.f (stopC 111 8)[k.val].a)
          (II.f (stopC 111 8)[k.val].b) (II.f (stopC 111 8)[k.val].c) := by
      apply allFin
      decide +kernel
    exact fun k hk => h ⟨k, hk⟩
  have hf : FrameOK leaveMemory 4096 256 := ⟨by decide, fun _ _ => rfl, fun _ _ => rfl⟩
  have hw : WeltAt leaveMemory callLayout world := by
    refine ⟨(fun t => nomatch t), (fun g => ⟨64, ?_, rfl⟩), (fun _ _ _ => rfl)⟩
    cases g
    decide +kernel
  have hs : Stops ⟨2048, 4096⟩ leaveMemory 111 :=
    stop_ok hc (by unfold CodeFar; decide) hf (by decide) (by decide) (by decide)
  intro n
  apply forever_runtime () (fun σ ρ => .leave rfl σ ρ) (fun σ ρ => (σ, true)) (entry := fun _ m σ ρ =>
    m = leaveMemory ∧ σ = world ∧ ρ = Env.nil) (lower := by decide)
  · intro m σ ρ he
    obtain ⟨rfl, rfl, rfl⟩ := he
    exact hs
  · intro n m σ ρ he bad
    contradiction
  · intro n m σ ρ he good
    obtain ⟨rfl, rfl, rfl⟩ := he
    exact ⟨leaveMemory, Star.refl _ _, AgreeW.refl _ _ _ _ _,
      (fun _ x => nomatch x), hw, Keeps.refl _ _ _⟩
  · exact ⟨rfl, rfl, rfl⟩

end Gabbro.Stage0.Senke.ReservedCallProbe

namespace Gabbro.Stage0.Senke.SourcePassProbe
open Gabbro.Grammatik Runner.IR Runner.Mem FnptrProben
set_option maxRecDepth 100000

/-- A real world store followed by an actual call, sharing a reserved caller frame. -/
def body : Block D (vertragVon D 2) true [] [] [] :=
  .cons (.assignGlob () pointer rfl (by intro w h; cases h))
    (.cons (.call 0 .nil (fit 2) rfl) .nil)

def lowered := lowB (reserved := 4) 1 addresses callLayout 4 ([ci 1 5 1 0], 6) [4] (0, 0) body
def bodyCode : List II := (lowered.getD ([], 0)).1

def code : List II := [ci 1 8 1 0] ++ [ci 19 8 (16 * (bodyCode.length + 2)) 0] ++ bodyCode ++ [ci 18 64 0 0] ++ stopC 104 8
def top : Nat := (lowered.getD ([], 0)).2

def image : List II := code ++ [ci 18 (-(16 * (code.length : Int))) 0 0]

def memory : Runner.Mem := { callMem with
  b := fun a => if 2048 ≤ a.toNat ∧ a.toNat < 2048 + 16 * image.length then
      ((image.flatMap encII)[a.toNat - 2048]?).getD 0 else if a.toNat = 4128 then 77 else callMem.b a }

theorem lowering : lowB (reserved := 4) 1 addresses callLayout 4 ([ci 1 5 1 0], 6) [4] (0, 0) body = some (bodyCode, top) := by
  decide +kernel

local instance (m : Runner.Mem) (pc : Runner.W) (o : Nat) (a b c : BitVec 32) :
    Decidable (InsAt m pc o a b c) :=
  if h : m.rd8 pc = some (BitVec.ofNat 8 o) ∧ m.rd32 (pc + 4) = some a ∧
      m.rd32 (pc + 8) = some b ∧ m.rd32 (pc + 12) = some c then
    .isTrue ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  else .isFalse (fun h' => h ⟨h'.op, h'.f1, h'.f2, h'.f3⟩)

theorem code_at : CodeAt memory 2048 code := by
  have h : ∀ k : Fin code.length, InsAt memory (2048 + BitVec.ofNat 64 (16 * k.val))
      code[k.val].o (II.f code[k.val].a) (II.f code[k.val].b) (II.f code[k.val].c) := by
    apply allFin
    decide +kernel
  exact fun k hk => h ⟨k, hk⟩

theorem functions_at : PCode memory addresses target 4096 256 := by
  have h : (List.finRange 3).all (fun f => (List.finRange (target f).length).all (fun k =>
      decide (InsAt memory (BitVec.ofNat 64 (addresses f) + BitVec.ofNat 64 (16 * k.val))
        (target f)[k.val].o (II.f (target f)[k.val].a) (II.f (target f)[k.val].b) (II.f (target f)[k.val].c)))) = true := by
    decide +kernel
  change ∀ f : Fin 3, CodeAt memory (BitVec.ofNat 64 (addresses f)) (target f) ∧
    CodeFar (BitVec.ofNat 64 (addresses f)) (target f).length 4096 256
  refine fun f => ⟨fun k hk => ?_, (targets_code f).2⟩
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp h f (by simp)) ⟨k, hk⟩ (by simp))

theorem frame : FrameOK memory 4096 256 := ⟨by decide, fun _ _ => rfl, fun _ _ => rfl⟩

theorem pre [Kern] : PreS callLayout memory 2048 4096 256 8 code (Env.nil : Env D []) 4 := by
  refine ⟨by decide, by decide, frame, code_at, ?_, (fun _ x => nomatch x), trivial, wstab_true _ _⟩
  unfold CodeFar
  decide +kernel

theorem world_at : WeltAt memory callLayout world := by
  refine ⟨(fun t => nomatch t), (fun g => ⟨64, ?_, rfl⟩), (fun _ _ _ => rfl)⟩
  cases g
  decide +kernel

theorem sync : SyncOK memory callLayout 4096 128 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide,
    (fun l => nomatch l), by decide, (fun l => nomatch l), (fun l => nomatch l), (fun l => nomatch l)⟩

theorem surroundings [Kern] : Umf callLayout addresses target 2 memory 4096 128 256 :=
  ⟨functions_at, by decide +kernel, by decide, sync, by decide⟩

theorem head : Kopf callLayout 2 memory 4096 256 0 0 (Env.nil : Env D []) tiny world :=
  ⟨by decide +kernel, by decide +kernel, (fun _ x => nomatch x), by decide, fun _ h => nomatch h⟩

local instance [Kern] : TorOK callLayout O where
  ans a := nomatch a
  puf a := nomatch a
local instance : SichtOK O := ⟨fun _ _ => rfl⟩

/-- A source invariant, a real world store and a real callee jointly use
    the generic pass theorem in the memory containing their actual instructions. -/
theorem forever_source_pass_zeuge [Kern] :
    ∃ m', Star ⟨2048, 4096⟩ memory
      ⟨2048 + BitVec.ofNat 64 (16 * code.length), 4096⟩ m' ∧
      WeltAt m' callLayout world ∧ m'.rd64 (slot 4096 4) = some 77 := by
  have hcb : lowB (reserved := 4) 1 addresses callLayout 4 ([ci 1 5 1 0], 6)
      [4] (exPlus (0, 0) 4) body = some (bodyCode, top) := by decide +kernel
  have h := forever_source_pass (reserved := 4) (O := O) (passes := 1)
    (P := tiny) (f := 2) (σ0 := world) (ρ0 := Env.nil) (lo := 4)
    (pr := [4]) (ex := (0, 0)) call_spec addresses_bound rfl rfl
    (show Expr D [] [] .bool from .tru) body rfl hcb
    (by decide) (by decide +kernel) (by decide) (by decide +kernel)
    call_win (by decide) (by decide)
    (by intro j hj; simp only [List.mem_singleton] at hj; subst j; decide)
    (by
      intro cb tb hcb htb hs hW m pc σ ρ hp hlo hlo2 hu hk hw hpr
      exact lowB_ok call_spec addresses_bound rfl rfl body cb tb hcb htb hs
        hW m pc σ ρ hp hlo hlo2 hu hk hw hpr)
    pre surroundings head world_at
  obtain ⟨m', run, _, _, world', keeps⟩ := h
  exact ⟨m', run, world', (keeps 4 (by simp)).trans (by decide +kernel)⟩

end Gabbro.Stage0.Senke.SourcePassProbe
