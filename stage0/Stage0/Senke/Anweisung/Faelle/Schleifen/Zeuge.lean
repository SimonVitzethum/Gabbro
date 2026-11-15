/- A jointly inhabited statement simulation: a real frame, function code, world and two condition checks. -/
module
public import Stage0.Senke.Ausdruck.Zeiger.FnptrAufrufProben
@[expose] public section


namespace Gabbro.Stage0.Senke.RetryProbe
open Gabbro.Grammatik Runner.IR Runner.Mem FnptrProben
set_option maxRecDepth 100000

/-- Next consumes one attempt; the changed boolean then ends retry successfully. -/
def statement : Stmt D (vertragVon D 2) false [.bool] [] [] :=
  .retry 2 (.var .here) (.cons (.assignVar .here .tru) (.cons (.next rfl) .nil)) .nil

def code : List II := ((lowS (reserved := 2) 1 addresses callLayout (functionFrame tiny 2) ([ci 1 5 1 0], 6) [] (0, 0) statement).getD ([], 0)).1

def memory : Runner.Mem := { callMem with
  b := fun a => if 2048 ≤ a.toNat ∧ a.toNat < 2048 + 16 * code.length then
      ((code.flatMap encII)[a.toNat - 2048]?).getD 0 else callMem.b a }

theorem lowered : lowS (reserved := 2) 1 addresses callLayout (functionFrame tiny 2) ([ci 1 5 1 0], 6) [] (0, 0) statement = some (code, 8) := by
  decide +kernel

local instance (m : Runner.Mem) (pc : Runner.W) (o : Nat) (a b c : BitVec 32) :
    Decidable (InsAt m pc o a b c) :=
  if h : m.rd8 pc = some (BitVec.ofNat 8 o) ∧ m.rd32 (pc + 4) = some a ∧
      m.rd32 (pc + 8) = some b ∧ m.rd32 (pc + 12) = some c then
    .isTrue ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  else .isFalse (fun h' => h ⟨h'.op, h'.f1, h'.f2, h'.f3⟩)

theorem code_at : CodeAt memory 2048 code := by
  refine codeAt_bytes code 2048 (by decide) ?_
  intro i hi
  have length := flatMap_enc_len code
  have room : 2048 + 16 * code.length < 2 ^ 64 := by decide
  have small : 2048 + i < 2 ^ 64 := by omega
  refine ⟨rfl, rfl, ?_⟩
  simp only [memory, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small,
    if_pos (by omega : 2048 ≤ 2048 + i ∧ 2048 + i < 2048 + 16 * code.length),
    Nat.add_sub_cancel_left, List.getElem?_eq_getElem hi, Option.getD_some]

theorem functions_at : PCode memory addresses target 4096 256 := by
  have changed : Agree 2048 0 (2 * code.length) callMem memory := by
    refine ⟨rfl, rfl, ?_⟩
    intro a outside
    simp only [memory]
    split
    · next inside => exfalso; simp only [inSlots, BitVec.toNat_ofNat, show (2048 : BitVec 64).toNat = 2048 from rfl] at outside; omega
    · rfl
  have below : ∀ f : Fin 3, addresses f + 16 * (target f).length ≤ 2048 := by
    apply allFin
    decide
  change ∀ f : Fin 3, CodeAt memory (BitVec.ofNat 64 (addresses f)) (target f) ∧
    CodeFar (BitVec.ofNat 64 (addresses f)) (target f).length 4096 256
  intro f
  refine ⟨(targets_code f).1.agree changed ?_, (targets_code f).2⟩
  have bound := below f
  have address := addresses_bound f
  simp only [CodeFar, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : addresses f < 2 ^ 64),
    show (2048 : BitVec 64).toNat = 2048 from rfl]
  constructor
  · omega
  · constructor
    · have room : 2048 + 16 * code.length < 2 ^ 64 := by decide
      omega
    · omega

theorem frame : FrameOK memory 4096 256 := ⟨by decide, fun _ _ => rfl, fun _ _ => rfl⟩

theorem pre [Kern] : PreS callLayout memory 2048 4096 256 7 code (Env.cons (τ := .bool) false Env.nil) 2 := by
  refine ⟨by decide, by decide, frame, code_at, ?_, ?_, trivial, wstab_true _ _⟩
  · unfold CodeFar; decide +kernel
  · apply envAt_cons
    · intro _ x; nomatch x
    · exact ValueAt.of_enc (w := 0) (by decide) (by decide +kernel) rfl

theorem world_at [Kern] : WeltAt memory callLayout world := by
  refine ⟨(fun t => nomatch t), (fun g => ?_), (fun _ _ _ => rfl)⟩
  cases g
  exact ValueAt.ofCellWord (w := 64) (by decide) (by decide +kernel) rfl

theorem sync : TicketSync memory callLayout 4096 128 [] :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide,
    (fun l => nomatch l), by decide, (fun l => nomatch l), (fun l => nomatch l), (fun l => nomatch l)⟩

theorem surroundings [Kern] : Umf callLayout addresses target 2 memory 4096 128 256 [] :=
  ⟨functions_at, by decide +kernel, by decide, sync, by decide⟩

theorem head : Kopf callLayout 2 memory 4096 256 0 0 (Env.nil : Env D []) tiny world :=
  ⟨by decide +kernel, by decide +kernel, (fun _ x => nomatch x), by decide, trivial⟩

local instance [Kern] : TorOK callLayout O where
  ans a := nomatch a
  puf a := nomatch a
  ref_answer a := nomatch a
  area a := nomatch a

local instance : SichtOK O := ⟨fun _ _ => rfl⟩

/-- The general retry proof has all premises together, and next reaches a true second check. -/
theorem retry_case_zeuge [Kern] :
    lowS (reserved := 2) 1 addresses callLayout (functionFrame tiny 2) ([ci 1 5 1 0], 6) [] (0, 0) statement = some (code, 8) ∧
    PreS callLayout memory 2048 4096 256 7 code (Env.cons (τ := .bool) false Env.nil) 2 ∧
    WIn callLayout 4096 128 256 ∧ Umf callLayout addresses target 2 memory 4096 128 256 [] ∧
    Kopf callLayout 2 memory 4096 256 0 0 (Env.nil : Env D []) tiny world ∧ WeltAt memory callLayout world ∧
    Sim callLayout tiny 2 world Env.nil 0 0 4096 4 256 [] ⟨2048, 4096⟩ memory
      (2048 + BitVec.ofNat 64 (16 * code.length)) (2048 + BitVec.ofNat 64 (16 * code.length))
      (2048 + BitVec.ofNat 64 (16 * code.length))
      (execStmt O 1 (rufAt tiny O 1 2) statement world (Env.cons (τ := .bool) false Env.nil)) 2 := by
  refine ⟨lowered, pre, call_win, surroundings, head, world_at, ?_⟩
  have h := lowS_ok (O := O) (passes := 1) (P := tiny) (f := 2) (σ0 := world)
    (ρ0 := Env.nil) (reserved := 2) (lo := 4) (pr := []) (ex := (0, 0)) call_spec addresses_bound rfl rfl scopes_nil statement HeldIn.nil code 8
    lowered (by decide) (by decide +kernel) call_win memory 2048 world (Env.cons (τ := .bool) false Env.nil)
    pre (by decide) (by decide) surroundings head world_at (fun _ h => nomatch h)
  simpa using h

end Gabbro.Stage0.Senke.RetryProbe
