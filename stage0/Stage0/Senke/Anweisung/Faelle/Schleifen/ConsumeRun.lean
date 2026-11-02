/- Joint generic correctness witnesses on emitted bytes and two real table cells. -/
module
public import Stage0.Senke.Anweisung.Faelle.Schleifen.ConsumeProbe
public section

namespace Gabbro.Stage0.Senke.ConsumeProbe
open Gabbro.Grammatik Runner.IR Runner.Mem
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem layout_in : LayIn layout := by
  refine ⟨?_, (fun g => nomatch g), by decide⟩
  intro t f k hk
  cases t
  cases f
  change (k : Int) < 2 at hk
  change 8192 ≤ 8192 + 8 * k ∧ 8192 + 8 * k + 8 ≤ 8208
  omega

theorem layout_dis : LayDis layout := by
  refine ⟨?_, ?_, ?_⟩
  · intro c c' hc hc' hne
    cases c with
    | glob g => nomatch g
    | elem t f k =>
      cases t
      cases f
      cases c' with
      | glob g => nomatch g
      | elem t' f' k' =>
        cases t'
        cases f'
        have hk : k ≠ k' := fun h => hne (by subst k'; rfl)
        change 8192 + 8 * k + 8 ≤ 8192 + 8 * k' ∨
          8192 + 8 * k' + 8 ≤ 8192 + 8 * k
        omega
  · intro c c' hc hc' he
    cases c with
    | glob g => nomatch g
    | elem t f k =>
      cases t
      cases f
      cases c' with
      | glob g => nomatch g
      | elem t' f' k' =>
        cases t'
        cases f'
        change 8192 + 8 * k = 8192 + 8 * k' at he
        have hk : k = k' := by omega
        subst k'
        rfl
  · intro c hc
    cases c with
    | glob g => nomatch g
    | elem t f k =>
      cases t
      cases f
      change (8192 + 8 * k) % 8 = 8192 % 8
      omega

theorem code_at (good : Bool) : CodeAt (memory good) 0 (code good) := by
  have all : (List.finRange (code good).length).all (fun k => decide
      ((memory good).rd8 (BitVec.ofNat 64 (16 * k.val)) = some (BitVec.ofNat 8 (code good)[k.val].o) ∧
       (memory good).rd32 (BitVec.ofNat 64 (16 * k.val) + 4) = some (II.f (code good)[k.val].a) ∧
       (memory good).rd32 (BitVec.ofNat 64 (16 * k.val) + 8) = some (II.f (code good)[k.val].b) ∧
       (memory good).rd32 (BitVec.ofNat 64 (16 * k.val) + 12) = some (II.f (code good)[k.val].c))) = true := by
    cases good <;> decide +kernel
  intro k hk
  have h := of_decide_eq_true (List.all_eq_true.mp all ⟨k, hk⟩ (by simp))
  simpa only [BitVec.zero_add] using (show InsAt (memory good)
    (BitVec.ofNat 64 (16 * k)) (code good)[k].o (II.f (code good)[k].a)
      (II.f (code good)[k].b) (II.f (code good)[k].c) from ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩)

theorem functions_at (good : Bool) :
    PCode (memory good) (fun _ => 2048) (fun _ => functionCode) 4096 64 := by
  intro f
  refine ⟨?_, by unfold CodeFar; decide⟩
  have all : (List.finRange functionCode.length).all (fun k => decide
      ((memory good).rd8 (2048 + BitVec.ofNat 64 (16 * k.val)) = some (BitVec.ofNat 8 functionCode[k.val].o) ∧
       (memory good).rd32 (2048 + BitVec.ofNat 64 (16 * k.val) + 4) = some (II.f functionCode[k.val].a) ∧
       (memory good).rd32 (2048 + BitVec.ofNat 64 (16 * k.val) + 8) = some (II.f functionCode[k.val].b) ∧
       (memory good).rd32 (2048 + BitVec.ofNat 64 (16 * k.val) + 12) = some (II.f functionCode[k.val].c))) = true := by
    cases good <;> decide +kernel
  intro k hk
  have h := of_decide_eq_true (List.all_eq_true.mp all ⟨k, hk⟩ (by simp))
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩

theorem frame (good : Bool) : FrameOK (memory good) 4096 64 :=
  ⟨by decide, fun _ _ => rfl, fun _ _ => rfl⟩

theorem pre [Kern] (good : Bool) :
    PreS layout (memory good) 0 4096 64 4 (code good) (Env.nil : Env D []) := by
  refine ⟨by decide, by decide, frame good, code_at good, ?_, ?_, trivial, wstab_true _ _⟩
  · unfold CodeFar
    cases good <;> decide +kernel
  · intro _ x; nomatch x

theorem world_at [Kern] (good : Bool) : WeltAt (memory good) layout initial := by
  refine ⟨?_, (fun g => nomatch g), fun _ _ _ => rfl⟩
  intro t f k hk
  cases t
  cases f
  change (k : Int) < 2 at hk
  have casesK : k = 0 ∨ k = 1 := by omega
  rcases casesK with rfl | rfl
  · exact ValueAt.ofCellWord (w := 1) (by decide) (by cases good <;> decide +kernel) rfl
  · exact ValueAt.ofCellWord (w := 1) (by decide) (by cases good <;> decide +kernel) rfl

theorem within [Kern] : WIn layout 4096 64 64 :=
  ⟨layout_in, layout_dis, by decide, by decide, by decide⟩

theorem sync (good : Bool) : SyncOK (memory good) layout 4096 64 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide,
    (fun l => nomatch l), by decide, (fun l => nomatch l),
    (fun l => nomatch l), (fun l => nomatch l)⟩

theorem surroundings [Kern] (good : Bool) :
    Umf layout (fun _ => 2048) (fun _ => functionCode) 0 (memory good) 4096 64 64 :=
  ⟨functions_at good, by cases good <;> decide +kernel, by decide, sync good, by decide⟩

theorem head (good : Bool) :
    Kopf layout () (memory good) 4096 64 0 0 (Env.nil : Env D []) program initial :=
  ⟨by cases good <;> decide +kernel, by cases good <;> decide +kernel,
    (fun _ x => nomatch x), by decide, trivial⟩

local instance [Kern] : TorOK layout oracle where
  ans a := nomatch a
  puf a := nomatch a
local instance : SichtOK oracle := ⟨fun _ _ => rfl⟩

theorem functions_spec [Kern] :
    FunSpec layout (fun _ => 2048) (fun _ => functionCode) calls 0 8 := by
  refine ⟨rfl, ?_⟩
  intro f m fp K Ks rp cfp σ ρ hc hW hK hF hC _ _ _ _ _ _
  exact stop_ok (hC f).1 (hC f).2 hF (by have := hW.ks; omega) hK (by decide)

/-- Both emitted sweeps instantiate the generic lowS_ok theorem with all
    premises jointly witnessed, including function code and call contract. -/
theorem consumeTraverse_case_zeuge [Kern] (good : Bool) :
    lowered good = some (code good, top good) ∧
    PreS layout (memory good) 0 4096 64 4 (code good) (Env.nil : Env D []) ∧
    WeltAt (memory good) layout initial ∧
    Sim layout program () initial .nil 0 0 4096 4 64 [3] ⟨0, 4096⟩ (memory good)
      (BitVec.ofNat 64 (16 * (code good).length))
      (BitVec.ofNat 64 (16 * (code good).length))
      (BitVec.ofNat 64 (16 * (code good).length))
      (execStmt oracle 1 calls (statement good) initial .nil) := by
  have emitted : lowered good = some (code good, top good) := by
    cases good <;> decide +kernel
  refine ⟨emitted, pre good, world_at good, ?_⟩
  have h := lowS_ok (O := oracle) (passes := 1) (P := program) (f := ())
    (σ0 := initial) (ρ0 := Env.nil) (lo := 4) (pr := [3]) (ex := (0, 0))
    (cens := post.1) (tens := post.2)
    functions_spec (by intro f; decide) rfl (by decide +kernel)
    (statement good) (code good) (top good) emitted
    (by cases good <;> decide +kernel) (by cases good <;> decide +kernel)
    within (memory good) 0 initial .nil (pre good) (by decide) (by decide)
    (surroundings good) (head good) (world_at good)
    (by
      intro j hj
      have e : j = 3 := by simpa using hj
      subst j
      decide)
  simpa using h

/-- The two actual stores remove both members and preserve the sentinel. -/
theorem consumeTraverse_run_zeuge [Kern] :
    ∃ m', Star ⟨0, 4096⟩ (memory true)
      ⟨BitVec.ofNat 64 (16 * (code true).length), 4096⟩ m' ∧
      m'.rd64 8192 = some 0 ∧ m'.rd64 8200 = some 0 ∧
      m'.rd64 (slot 4096 3) = some 77 := by
  have run := (consumeTraverse_case_zeuge true).2.2.2
  change Reach layout 4096 4 64 [3] ⟨0, 4096⟩ (memory true)
    (BitVec.ofNat 64 (16 * (code true).length)) afterSecond .nil at run
  obtain ⟨m', steps, _, _, represented, kept⟩ := run
  obtain ⟨w0, read0, enc0⟩ := ValueAt.word (D.typ () ()) _
    (wordCompatB_sound _ (by decide)) (represented.1 () () 0 (by decide))
  obtain ⟨w1, read1, enc1⟩ := ValueAt.word (D.typ () ()) _
    (wordCompatB_sound _ (by decide)) (represented.1 () () 1 (by decide))
  have e0 : w0 = 0 := enc0
  have e1 : w1 = 0 := enc1
  rw [slot_zero] at read0 read1
  refine ⟨m', steps, ?_, ?_, ?_⟩
  · simpa only [e0] using read0
  · simpa only [e1] using read1
  · exact (kept 3 (by simp)).trans (by decide +kernel)

/-- An invariant failure produces the existing runner exit_group(104). -/
theorem consumeTraverse_stop_zeuge [Kern] : Stops ⟨0, 4096⟩ (memory false) 104 := by
  have run := (consumeTraverse_case_zeuge false).2.2.2
  exact run

end Gabbro.Stage0.Senke.ConsumeProbe
