/- A real world store and call preserve a live sentinel in a nonzero reserved frame. -/
import Stage0.Senke.Ausdruck.FnptrAufrufProben

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

def memory : Runner.Mem := { callMem with
  b := fun a => if 2048 ≤ a.toNat ∧ a.toNat < 2048 + 16 * code.length then
      ((code.flatMap encII)[a.toNat - 2048]?).getD 0 else if a.toNat = 4128 then 77 else callMem.b a }

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

local instance [Kern] : TorOK callLayout O where
  ans a := nomatch a
  puf a := nomatch a
local instance : SichtOK O := ⟨fun _ _ => rfl⟩

/-- All premises hold together; the actual write and callee preserve the live reserved sentinel. -/
theorem write_call_reserved_zeuge [Kern] :
    ∃ m', Star ⟨2048, 4096⟩ memory
      ⟨2048 + BitVec.ofNat 64 (16 * code.length), 4096⟩ m' ∧
      m'.rd64 (slot 4096 (BitVec.ofNat 64 4)) = some 77 := by
  have h := lowB_ok (reserved := 4) (O := O) (passes := 1) (P := tiny) (f := 2)
    (σ0 := world) (ρ0 := Env.nil) (lo := 4) (pr := [4]) (ex := (0, 0))
    call_spec addresses_bound rfl rfl body code top lowering (by decide +kernel)
    (by decide +kernel) call_win memory 2048 world Env.nil pre (by decide) (by decide)
    surroundings head world_at (by intro j hj; simp only [List.mem_singleton] at hj; subst j; decide)
  change Reach callLayout 4096 4 256 [4] ⟨2048, 4096⟩ memory
    (2048 + BitVec.ofNat 64 (16 * code.length)) _ Env.nil 4 at h
  obtain ⟨m', hs, _, _, _, hk⟩ := h
  refine ⟨m', hs, ?_⟩
  rw [hk 4 (by simp)]
  decide +kernel

end Gabbro.Stage0.Senke.ReservedCallProbe
