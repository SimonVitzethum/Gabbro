/- A real world store and call preserve a live sentinel in a nonzero reserved frame. -/
import Stage0.Senke.Ausdruck.FnptrAufrufProben
import Stage0.Senke.Anweisung.Faelle.Schleifen.Runtime

namespace Gabbro.Stage0.Senke.CounterCallProbe
open Gabbro.Grammatik Runner.IR Runner.Mem FnptrProben
set_option maxRecDepth 2000

/-- A real world store followed by an actual call, sharing a reserved caller frame. -/
def body : Block D (vertragVon D 2) false [] [] [] :=
  .cons (.assignGlob () pointer rfl (by intro w h; cases h))
    (.cons (.call 0 .nil (fit 2) rfl) .nil)

def lowered := lowB (reserved := 4) 1 addresses callLayout 4 ([ci 1 5 1 0], 6) [4, 5, 6] (0, 0) body
def code : List II := (lowered.getD ([], 0)).1
def top : Nat := (lowered.getD ([], 0)).2

def image : List II :=
  [ci 19 6 (16 * (code.length + 3 : Nat)) 0, ci 4 6 6 5] ++
  code ++ [ci 18 (-(16 * (code.length + 2 : Nat))) 0 0] ++ stopC 111 8

def memory : Runner.Mem := { callMem with
  b := fun a => if 2016 ≤ a.toNat ∧ a.toNat < 2016 + 16 * image.length then
      ((image.flatMap encII)[a.toNat - 2016]?).getD 0 else if a.toNat = 4128 then 77 else if a.toNat = 4136 then 1 else callMem.b a }

theorem lowering : lowB (reserved := 4) 1 addresses callLayout 4 ([ci 1 5 1 0], 6) [4, 5, 6] (0, 0) body = some (code, top) := by
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

/-- The generic block theorem supplies the complete runtime and frame result. -/
theorem body_simulation [Kern] :
    Reach callLayout 4096 4 256 [4, 5, 6] ⟨2048, 4096⟩ memory
      (2048 + BitVec.ofNat 64 (16 * code.length)) world Env.nil 4 := by
  have h := lowB_ok (reserved := 4) (O := O) (passes := 1) (P := tiny) (f := 2)
    (σ0 := world) (ρ0 := Env.nil) (lo := 4) (pr := [4, 5, 6]) (ex := (0, 0))
    call_spec addresses_bound rfl rfl body code top lowering (by decide +kernel)
    (by decide +kernel) call_win memory 2048 world Env.nil pre (by decide) (by decide)
    surroundings head world_at (by intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; rcases hj with rfl | rfl | rfl <;> decide)
  change Reach callLayout 4096 4 256 [4, 5, 6] ⟨2048, 4096⟩ memory
    (2048 + BitVec.ofNat 64 (16 * code.length)) _ Env.nil 4 at h
  exact h

/-- Reuse the emitted block in the memory produced by a previous pass. -/
theorem body_simulation_at [Kern] {m : Runner.Mem}
    (hp : PreS callLayout m 2048 4096 256 8 code (Env.nil : Env D []) 4)
    (hu : Umf callLayout addresses target 2 m 4096 128 256)
    (hk : Kopf callLayout 2 m 4096 256 0 0 (Env.nil : Env D []) tiny world)
    (hw : WeltAt m callLayout world) :
    Reach callLayout 4096 4 256 [4, 5, 6] ⟨2048, 4096⟩ m
      (2048 + BitVec.ofNat 64 (16 * code.length)) world Env.nil 4 := by
  have h := lowB_ok (reserved := 4) (O := O) (passes := 1) (P := tiny) (f := 2)
    (σ0 := world) (ρ0 := Env.nil) (lo := 4) (pr := [4, 5, 6]) (ex := (0, 0))
    call_spec addresses_bound rfl rfl body code top lowering (by decide +kernel)
    (by decide +kernel) call_win m 2048 world Env.nil hp (by decide) (by decide)
    hu hk hw (by intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; rcases hj with rfl | rfl | rfl <;> decide)
  exact h

/-- The emitted body jointly retains the sentinel, unit and budget cells.
    This frame is obtained from the real world write and reachable callee. -/
theorem body_controls_zeuge [Kern] :
    ∃ m', Star ⟨2048, 4096⟩ memory
      ⟨2048 + BitVec.ofNat 64 (16 * code.length), 4096⟩ m' ∧
      Keeps 4096 [4, 5, 6] memory m' ∧
      m'.rd64 (slot 4096 (BitVec.ofNat 64 4)) = some 77 ∧
      m'.rd64 (slot 4096 (BitVec.ofNat 64 5)) = some 1 := by
  obtain ⟨m', run, _, _, _, kept⟩ := body_simulation
  refine ⟨m', run, kept, ?_, ?_⟩
  · rw [kept 4 (by simp)]; decide +kernel
  · rw [kept 5 (by simp)]; decide +kernel

/-- The same constant-size image with each of the three small semantic budgets. -/
def loaded (budget : Fin 3) : Runner.Mem :=
  write memory (slot 4096 (BitVec.ofNat 64 6)) 8 budget.val

theorem loaded_code (budget : Fin 3) : CodeAt (loaded budget) 2048 code := by
  have h : ∀ b : Fin 3, ∀ k : Fin code.length,
      InsAt (loaded b) (2048 + BitVec.ofNat 64 (16 * k.val))
        code[k.val].o (II.f code[k.val].a) (II.f code[k.val].b) (II.f code[k.val].c) := by
    apply allFin
    decide +kernel
  exact fun k hk => h budget ⟨k, hk⟩

theorem loaded_frame (budget : Fin 3) : FrameOK (loaded budget) 4096 256 :=
  ⟨by decide, fun _ _ => rfl, fun _ _ => rfl⟩

theorem loaded_pre [Kern] (budget : Fin 3) :
    PreS callLayout (loaded budget) 2048 4096 256 8 code (Env.nil : Env D []) 4 :=
  ⟨pre.ctx, pre.small, loaded_frame budget, loaded_code budget, pre.far,
    (fun _ x => nomatch x), trivial, wstab_true _ _⟩

theorem loaded_world (budget : Fin 3) : WeltAt (loaded budget) callLayout world := by
  refine ⟨(fun t => nomatch t), (fun g => ⟨64, ?_, rfl⟩), (fun _ _ _ => rfl)⟩
  cases g
  have h : ∀ b : Fin 3, (loaded b).rd64 8192 = some 64 := by
    apply allFin
    decide +kernel
  exact h budget

theorem loaded_functions (budget : Fin 3) :
    PCode (loaded budget) addresses target 4096 256 := by
  have h : ∀ b : Fin 3, (List.finRange 3).all (fun f =>
      (List.finRange (target f).length).all (fun k => decide
        (InsAt (loaded b) (BitVec.ofNat 64 (addresses f) + BitVec.ofNat 64 (16 * k.val))
        (target f)[k.val].o (II.f (target f)[k.val].a)
        (II.f (target f)[k.val].b) (II.f (target f)[k.val].c)))) = true := by
    apply allFin
    decide +kernel
  change ∀ f : Fin 3, CodeAt (loaded budget) (BitVec.ofNat 64 (addresses f)) (target f) ∧
    CodeFar (BitVec.ofNat 64 (addresses f)) (target f).length 4096 256
  refine fun f => ⟨fun k hk => ?_, (targets_code f).2⟩
  exact of_decide_eq_true (List.all_eq_true.mp
    (List.all_eq_true.mp (h budget) f (by simp)) ⟨k, hk⟩ (by simp))

theorem loaded_surroundings [Kern] (budget : Fin 3) :
    Umf callLayout addresses target 2 (loaded budget) 4096 128 256 := by
  refine ⟨loaded_functions budget, ?_, by decide, ?_, by decide⟩
  · have h : ∀ b : Fin 3, (loaded b).rd64 (slot 4096 2) = some 3 := by
      apply allFin
      decide +kernel
    exact h budget
  · exact ⟨by decide, by decide, by decide, by decide, by decide, by decide,
      (fun l => nomatch l), by decide, (fun l => nomatch l),
      (fun l => nomatch l), (fun l => nomatch l)⟩

theorem loaded_head (budget : Fin 3) :
    Kopf callLayout 2 (loaded budget) 4096 256 0 0 (Env.nil : Env D []) tiny world := by
  refine ⟨?_, ?_, (fun _ x => nomatch x), by decide, fun _ h => nomatch h⟩
  · have h : ∀ b : Fin 3, (loaded b).rd64 (slot 4096 0) = some 0 := by
      apply allFin
      decide +kernel
    exact h budget
  · have h : ∀ b : Fin 3, (loaded b).rd64 (slot 4096 1) = some 0 := by
      apply allFin
      decide +kernel
    exact h budget

end Gabbro.Stage0.Senke.CounterCallProbe
