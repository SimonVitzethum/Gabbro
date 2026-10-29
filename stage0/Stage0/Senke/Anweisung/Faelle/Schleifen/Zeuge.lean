/- A jointly inhabited statement simulation: a real frame, function code, world and two condition checks. -/
import Stage0.Senke.Ausdruck.FnptrAufrufProben

namespace Gabbro.Stage0.Senke.RetryProbe
open Gabbro.Grammatik Runner.IR Runner.Mem FnptrProben
set_option maxRecDepth 100000

/-- Next consumes one attempt; the changed boolean then ends retry successfully. -/
def statement : Stmt D (vertragVon D 2) false [.bool] [] [] :=
  .retry 2 (.var .here) (.cons (.assignVar .here .tru) (.cons (.next rfl) .nil)) .nil

def code : List II := ((lowS addresses callLayout 3 ([ci 1 4 1 0], 5) [] (0, 0) statement).getD ([], 0)).1

def memory : Runner.Mem := { callMem with
  b := fun a => if 2048 ≤ a.toNat ∧ a.toNat < 2048 + 16 * code.length then
      ((code.flatMap encII)[a.toNat - 2048]?).getD 0 else callMem.b a }

theorem lowered : lowS addresses callLayout 3 ([ci 1 4 1 0], 5) [] (0, 0) statement = some (code, 5) := by
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

theorem pre [Kern] : PreS callLayout memory 2048 4096 256 4 code (Env.cons (τ := .bool) false Env.nil) := by
  refine ⟨by decide, by decide, frame, code_at, ?_, ?_, trivial, wstab_true _ _⟩
  · unfold CodeFar; decide +kernel
  · apply envAt_cons (w := 0)
    · intro _ x; nomatch x
    · decide +kernel
    · rfl

theorem world_at : WeltAt memory callLayout world := by
  refine ⟨(fun t => nomatch t), (fun g => ⟨64, ?_, rfl⟩), (fun _ _ _ => rfl)⟩
  cases g
  decide +kernel

theorem sync : SyncOK memory callLayout 4096 128 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide,
    (fun l => nomatch l), by decide, (fun l => nomatch l), (fun l => nomatch l), (fun l => nomatch l)⟩

theorem surroundings [Kern] : Umf callLayout addresses target 2 memory 4096 128 256 :=
  ⟨functions_at, by decide +kernel, by decide, sync, by decide⟩

theorem head : Kopf callLayout 2 memory 4096 256 0 0 (Env.nil : Env D []) :=
  ⟨by decide +kernel, by decide +kernel, (fun _ x => nomatch x), by decide⟩

local instance [Kern] : TorOK callLayout O where
  ans a := nomatch a
  puf a := nomatch a
local instance : SichtOK O := ⟨fun _ _ => rfl⟩

/-- The general retry proof has all premises together, and next reaches a true second check. -/
theorem retry_case_zeuge [Kern] :
    lowS addresses callLayout 3 ([ci 1 4 1 0], 5) [] (0, 0) statement = some (code, 5) ∧
    PreS callLayout memory 2048 4096 256 4 code (Env.cons (τ := .bool) false Env.nil) ∧
    WIn callLayout 4096 128 256 ∧ Umf callLayout addresses target 2 memory 4096 128 256 ∧
    Kopf callLayout 2 memory 4096 256 0 0 (Env.nil : Env D []) ∧ WeltAt memory callLayout world ∧
    Sim callLayout tiny 2 world Env.nil 0 0 4096 3 256 [] ⟨2048, 4096⟩ memory
      (2048 + BitVec.ofNat 64 (16 * code.length)) (2048 + BitVec.ofNat 64 (16 * code.length))
      (2048 + BitVec.ofNat 64 (16 * code.length))
      (execStmt O 1 (rufAt tiny O 1 2) statement world (Env.cons (τ := .bool) false Env.nil)) := by
  refine ⟨lowered, pre, call_win, surroundings, head, world_at, ?_⟩
  have h := lowS_ok (O := O) (passes := 1) (P := tiny) (f := 2) (σ0 := world)
    (ρ0 := Env.nil) (lo := 3) (pr := []) (ex := (0, 0)) call_spec addresses_bound rfl rfl statement code 5
    lowered (by decide) (by decide +kernel) call_win memory 2048 world (Env.cons (τ := .bool) false Env.nil)
    pre (by decide) (by decide) surroundings head world_at (fun _ h => nomatch h)
  simpa using h

end Gabbro.Stage0.Senke.RetryProbe
