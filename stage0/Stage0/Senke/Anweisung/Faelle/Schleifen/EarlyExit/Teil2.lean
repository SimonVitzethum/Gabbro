module

public import Stage0.Senke.Anweisung.Faelle.Schleifen.CounterRun
public import Stage0.Senke.Anweisung.Faelle.Schleifen.CountedLoop
public import Stage0.Senke.Anweisung.Faelle.Schleifen.StatementCost
public import Stage0.Senke.Anweisung.Faelle.Schleifen.EarlyExit.Teil1

@[expose] public section

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
    refine ⟨(fun t => nomatch t), (fun g => ?_), (fun _ _ _ => rfl)⟩
    cases g
    refine ValueAt.ofCellWord (w := 64) (by decide) ?_ rfl
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

/-- The loaded image jointly inhabits the normal backedge with both OWN words
    protected. The same memory already supports nonempty next/leave above. -/
theorem counter_dispatch_zeuge (P : Programm D) (σ0 : World D)
    (ρ0 : Env D (D.params 2)) :
    ∃ k m', k ≤ 1 ∧ Counted k ⟨2160, 4096⟩ (memory true) ⟨2224, 4096⟩ m' ∧
      AgreeW callLayout 4096 4 256 (memory true) m' ∧
      EnvAt callLayout m' 4096 (Env.nil : Env D []) 8 ∧
      WeltAt m' callLayout world ∧ Keeps 4096 [8, 9] (memory true) m' ∧
      ∀ j, j < 4 ∨ j ∈ [8, 9] →
        m'.rd64 (slot 4096 (BitVec.ofNat 64 j)) =
          (memory true).rd64 (slot 4096 (BitVec.ofNat 64 j)) := by
  obtain ⟨pre, inside, hw, around⟩ := joint true
  have body : CountedSim (l := true) 0 callLayout P 2 σ0 ρ0 3000 5000 4096 4 256 [8, 9]
      ⟨2160, 4096⟩ (memory true) 2160 2224 2224
      (.ok world (Env.nil : Env D [])) 8 := by
    change CountedReach 0 callLayout 4096 4 256 [8, 9] ⟨2160, 4096⟩
      (memory true) 2160 world (Env.nil : Env D []) 8
    exact ⟨memory true, Counted.refl _ _, AgreeW.refl _ _ _ _ _,
      (fun _ x => nomatch x), hw, Keeps.refl _ _ _⟩
  exact body.counter_dispatch inside (by decide)
    (jump := 64) (b := 0) (c := 0) (by decide +kernel)
    (by unfold CodeFar; decide +kernel) (by decide)

/-- A nonempty source next certificate protects both OWN words and reaches
    the same endpoint as the normal backedge witness. -/
theorem source_counter_dispatch_zeuge (P : Programm D) (σ0 : World D)
    (ρ0 : Env D (D.params 2)) :
    ∃ n, n ≤ 1 ∧ ∃ k m', k ≤ n + 1 ∧ Counted k ⟨2144, 4096⟩ (memory true) ⟨2224, 4096⟩ m' ∧
      AgreeW callLayout 4096 4 256 (memory true) m' ∧
      EnvAt callLayout m' 4096 (Env.nil : Env D []) 8 ∧
      WeltAt m' callLayout world ∧ Keeps 4096 [8, 9] (memory true) m' ∧
      ∀ j, j < 4 ∨ j ∈ [8, 9] →
        m'.rd64 (slot 4096 (BitVec.ofNat 64 j)) =
          (memory true).rd64 (slot 4096 (BitVec.ofNat 64 j)) := by
  obtain ⟨pre, inside, hw, around⟩ := joint true
  have code : CodeAt (memory true) 2144 [ci 18 80 0 0] := by
    intro k hk
    have : k = 0 := by simpa using hk
    subst k
    simp only [List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero, ci]
    exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
  have bp : PreS callLayout (memory true) 2144 4096 256 12
      [ci 18 80 0 0] (Env.nil : Env D []) 8 :=
    ⟨by decide, by decide, pre.frame, code,
      (by unfold CodeFar; decide +kernel), (fun _ x => nomatch x), trivial, wstab_true _ _⟩
  have cert : recursiveBlockCost callLayout 8 P 1 addresses (fun _ => []) 2 128
      (vertragVon D 2) true (LoopJumpCostProbe.body true) world Env.nil
      (.next rfl world Env.nil) 1 := .jump rfl true
  exact cert.counter_dispatch (σ0 := σ0) (ρ0 := ρ0) (rp := 3000) (cfp := 5000)
    (top := 12) (ens := ([], 6)) (ex := (64, 64)) (by decide +kernel) (by decide) inside (by decide)
    (by decide) (by decide) (by intro j hj; simp at hj; unfold frei FB; omega)
    bp around hw (jump := 64) (a := 0) (c := 0) (by decide +kernel)
    (by unfold CodeFar; decide +kernel) (by decide)

end Gabbro.Stage0.Senke.InitializedPassProbe

namespace Gabbro.Stage0.Senke.SourceStopProbe
open Gabbro.Grammatik Runner Runner.IR Runner.Mem
/-- Two nonempty next bodies and the zero-budget terminal share one source tree
    and one accepted body lowering. This is not a nested CALL/LOOP witness. -/
theorem nestedForever_next_zeuge [Kern] {D : Deklaration} (L : Lay D)
    (P : Programm D) (A : D.Fn → Nat) (C : D.Fn → List II)
    (V : Vertrag D) (assumption : D.Annahme) (σ : World D) :
    ∃ tree : NestedForever L 2 P 2 A C 0 32 V assumption
        (Expr.tru (Γ := []) (Λ := [])) (.cons (.next rfl) .nil)
        2 σ Env.nil (.hardware (.fortschritt assumption)) 13,
      lowB (reserved := 2) 2 A L 4 ([], 6) [4, 5] (64, -48)
        (Block.cons (V := V) (Γ := []) (Λ := []) (.next rfl) .nil) = some ([ci 18 (-32) 0 0], 6) ∧
      2 + 13 ≤ 5 + 2 * (5 + tree.childCharge) := by
  let tree : NestedForever L 2 P 2 A C 0 32 V assumption
      (Expr.tru (Γ := []) (Λ := [])) (.cons (.next rfl) .nil)
      2 σ Env.nil (.hardware (.fortschritt assumption)) 13 :=
    .next ExprCost.truth (.jump rfl true)
      (.next ExprCost.truth (.jump rfl true) .zero)
  exact ⟨tree, rfl, tree.structural_bound⟩
end Gabbro.Stage0.Senke.SourceStopProbe

namespace Gabbro.Stage0.Senke.PositiveInvariantStopProbe
set_option maxRecDepth 10000
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
  foreverCounter 8 9 160 ++ [ci 1 12 (if positive then 1 else 0) 0,
    ci 19 12 48 0, ci 18 (-64) 0 0, ci 18 64 0 0] ++
    stopC 104 12 ++ [ci 18 (-144) 0 0] ++ stopC 111 12
def memory (positive : Bool) : Mem :=
  let base := write (write callMem (slot 4096 8) 8 2) (slot 4096 9) 8 1
  { base with b := fun a => if 2048 ≤ a.toNat ∧ a.toNat < 2256 then
      (((image positive).flatMap encII)[a.toNat - 2048]?).getD 0 else base.b a }
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
    refine ⟨(fun t => nomatch t), (fun g => ?_), (fun _ _ _ => rfl)⟩
    cases g
    refine ValueAt.ofCellWord (w := 64) (by decide) ?_ rfl
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

/-- Positive fuel, false source invariant and a nonempty accepted body coexist
    on the actual full suffix; execution reaches the pending failure syscall. -/
theorem forever_positive_invariant_stop_counted_zeuge (P : Programm D) :
    CountedStops 6 ⟨2048, 4096⟩ (memory false) 104 := by
  obtain ⟨pre, inside, hw, around⟩ := joint false
  exact forever_positive_invariant_stop_counted
    (P := P) (f := 2) (passes := 1) (A := addresses) (C := fun _ => []) (dv := 2)
    (reserved := 8) (inv := .fls) (body := LoopJumpCostProbe.body true)
    (fuel := 1) (ni := 1) (lo := 4) (counter := 8) (one := 9)
    (ens := ([], 6)) (pr := []) (cc := [ci 1 12 0 0]) (cb := [ci 18 (-64) 0 0])
    (tc := 13) (tb := 12) ExprCost.falsity rfl (by decide +kernel)
    (by decide) (by decide) inside (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by intros; contradiction) (by decide)
    (by decide) pre around hw (by decide +kernel) (by decide +kernel) (by decide)

/-- The same full suffix with a true source invariant executes a nonempty next
    body and returns to the live header after the actual counter decrement. -/
theorem forever_full_positive_counted_zeuge (P : Programm D) (σ0 : World D)
    (ρ0 : Env D (D.params 2)) :
    ∃ n, n ≤ 5 ∧ CountedReach n callLayout 4096 4 256 []
      ⟨2048, 4096⟩ (memory true) 2048 world (Env.nil : Env D []) 8 := by
  obtain ⟨pre, inside, hw, around⟩ := joint true
  have child : recursiveBlockCost callLayout 8 P 1 addresses (fun _ => []) 2 128
      (vertragVon D 2) true (LoopJumpCostProbe.body true) world Env.nil
      (.next rfl world Env.nil) 1 := .jump rfl true
  have result := recursiveBlockCost.forever_full_positive_counted
    (σ0 := σ0) (ρ0 := ρ0) (rp := 3000) (cfp := 5000)
    (P := P) (f := 2) (passes := 1) (A := addresses) (C := fun _ => []) (dv := 2)
    (reserved := 8) (inv := .tru) (body := LoopJumpCostProbe.body true)
    (fuel := 1) (ni := 1) (lo := 4) (counter := 8) (one := 9)
    (ens := ([], 6)) (pr := []) (cc := [ci 1 12 1 0]) (cb := [ci 18 (-64) 0 0])
    (tc := 13) (tb := 12) ExprCost.truth child rfl (by decide +kernel)
    (by decide) (by decide) inside (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by intros; contradiction) (by decide)
    (by decide) pre around hw (by decide +kernel) (by decide +kernel) (by decide)

  have endpoint : (2048 : W) + 16 + 16 + BitVec.ofNat 64 (16 * 1) + 16 +
      BitVec.ofNat 64 (16 * 1) + BitVec.ofInt 64 (foreverTargets 1 1).2 = 2048 := by
    decide +kernel
  simpa only [CountedSim, List.length_singleton, endpoint] using result
end Gabbro.Stage0.Senke.PositiveInvariantStopProbe

namespace Gabbro.Stage0.Senke.NormalLoopSoundProbe
set_option maxRecDepth 10000
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
  [ci 1 10 2 0, ci 1 11 1 0] ++ foreverCounter 10 11 144 ++ [ci 1 12 (if positive then 1 else 0) 0,
    ci 19 12 32 0, ci 18 64 0 0] ++
    stopC 104 12 ++ [ci 18 (-128) 0 0] ++ stopC 111 12
def memory (positive : Bool) : Mem :=
  let base := write (write callMem (slot 4096 10) 8 2) (slot 4096 11) 8 1
  { base with b := fun a => if 2048 ≤ a.toNat ∧ a.toNat < 2272 then
      (((image positive).flatMap encII)[a.toNat - 2048]?).getD 0 else base.b a }
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
    refine ⟨(fun t => nomatch t), (fun g => ?_), (fun _ _ _ => rfl)⟩
    cases g
    refine ValueAt.ofCellWord (w := 64) (by decide) ?_ rfl
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

theorem sound_zeuge (P : Programm D) (σ0 : World D)
    (ρ0 : Env D (D.params 2)) :
    ∃ k, k ≤ 17 ∧ CountedStops k ⟨2048, 4096⟩ (memory true) 111 := by
  obtain ⟨pre, inside, hw, around⟩ := joint true
  have child : recursiveBlockCost callLayout 8 P 2 addresses (fun _ => []) 2 128
      (vertragVon D 2) true (Block.nil (Λ := [])) world Env.nil
      (.ok world Env.nil) 0 := .source .nil
  let tree : NestedForever callLayout 8 P 2 addresses (fun _ => []) 2 128
      (vertragVon D 2) () .tru (Block.nil (Λ := []))
      2 world Env.nil (.hardware (.fortschritt ())) 15 :=
    .normal .truth child (.normal .truth child .zero)
  have result := tree.accepted_sound
    (σ0 := σ0) (ρ0 := ρ0) (rp := 3000) (cfp := 5000)
    (f := 2) (lo := 4) (ens := ([], 6)) (pr := []) (ex := (0, 0))
    (code := image true) (top := 20)
    (by decide +kernel) (by decide) inside (by decide)
    (by intros; contradiction) (by decide) pre around hw
  simpa [tree, NestedForever.childCharge, CountedSim, hwCode] using result
end Gabbro.Stage0.Senke.NormalLoopSoundProbe
