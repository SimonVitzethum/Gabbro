/- A concrete overlapping move with six live variables and two nested counter pairs. -/
import Stage0.Senke.Anweisung.Faelle.Schleifen.Relocate
import Stage0.Senke.Ausdruck.FnptrAufrufProben

namespace Gabbro.Stage0.Senke.RelocateProbe
open Gabbro.Grammatik Runner Runner.IR Runner.Mem

def code := relocateC 4 4 6

def memory : Mem := {
  b := fun a => if a.toNat < 16 * code.length then
    ((code.flatMap encII)[a.toNat]?).getD 0
    else if a.toNat = 4128 ∨ a.toNat = 4144 ∨ a.toNat = 4160 then 1
    else if a.toNat = 4208 then 77 else 0
  rd := fun _ => true
  wr := fun _ => true }

def env {D : Deklaration} : Env D [.bool, .bool, .bool, .bool, .bool, .bool] :=
  .cons false (.cons true (.cons false (.cons true (.cons false (.cons true .nil)))))

local instance (m : Mem) (pc : W) (o : Nat) (a b c : BitVec 32) :
    Decidable (InsAt m pc o a b c) :=
  if h : m.rd8 pc = some (BitVec.ofNat 8 o) ∧ m.rd32 (pc + 4) = some a ∧
      m.rd32 (pc + 8) = some b ∧ m.rd32 (pc + 12) = some c then
    .isTrue ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  else .isFalse (fun h' => h ⟨h'.op, h'.f1, h'.f2, h'.f3⟩)

theorem code_at : CodeAt memory 0 code := by
  have h : ∀ k : Fin code.length, InsAt memory (BitVec.ofNat 64 (16 * k.val))
      code[k.val].o (II.f code[k.val].a) (II.f code[k.val].b) (II.f code[k.val].c) := by
    apply FnptrProben.allFin
    decide +kernel
  exact fun k hk => by simpa using h ⟨k, hk⟩

theorem frame : FrameOK memory 4096 32 :=
  ⟨by decide, fun _ _ => rfl, fun _ _ => rfl⟩

theorem env_at {D : Deklaration} (L : Lay D) : EnvAt L memory 4096 env 0 := by
  intro τ x
  cases x with
  | here => exact ⟨0, by decide +kernel, rfl⟩
  | there x => cases x with
    | here => exact ⟨1, by decide +kernel, rfl⟩
    | there x => cases x with
      | here => exact ⟨0, by decide +kernel, rfl⟩
      | there x => cases x with
        | here => exact ⟨1, by decide +kernel, rfl⟩
        | there x => cases x with
          | here => exact ⟨0, by decide +kernel, rfl⟩
          | there x => cases x with
            | here => exact ⟨1, by decide +kernel, rfl⟩
            | there x => nomatch x

/-- All six variables survive the actual overlapping Runner moves. The untouched
    sentinel follows from the exact frame, not from an additional assumption. -/
theorem relocate_env_zeuge [Kern] {D : Deklaration} (L : Lay D) :
    ∃ m', Star ⟨0, 4096⟩ memory ⟨96, 4096⟩ m' ∧ EnvAt L m' 4096 env 4 ∧
      m'.rd64 (slot 4096 14) = some 77 ∧
      (slot (4096 : W) 6).toNat = 4144 ∧ (slot (4096 : W) 7).toNat = 4152 := by
  obtain ⟨m', run, writes, shifted⟩ := relocate_env frame (by decide)
    (by decide) (env_at L) code_at (by unfold CodeFar; decide)
  refine ⟨m', run, shifted, ?_, by decide, by decide⟩
  change m'.rd64 (slot 4096 (BitVec.ofNat 64 14)) = some 77
  rw [agree_rd_high (i := 14) writes frame.room (by decide) (by decide)]
  decide +kernel

/-- The witness really copies an overlapping range in descending order. -/
theorem emitted_moves_zeuge : code =
    [ci 2 13 9 0, ci 2 12 8 0, ci 2 11 7 0,
     ci 2 10 6 0, ci 2 9 5 0, ci 2 8 4 0] := by decide

/-- Direct instantiation of the word-range Runner simulation on concrete bytes. -/
theorem relocate_run_zeuge [Kern] :
    ∃ m', Star ⟨0, 4096⟩ memory ⟨96, 4096⟩ m' ∧
      Agree 4096 8 14 memory m' ∧
      ∀ i, i < 6 → m'.rd64 (slot 4096 (BitVec.ofNat 64 (8 + i))) =
        memory.rd64 (slot 4096 (BitVec.ofNat 64 (4 + i))) := by
  exact relocate_run frame (by decide) (by decide) code_at (by unfold CodeFar; decide)

end Gabbro.Stage0.Senke.RelocateProbe
