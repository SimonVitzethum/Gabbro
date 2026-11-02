module
public import Stage0.Senke.Anweisung.Faelle.Schleifen.Counters.CounterRuna
public import Stage0.Senke.Anweisung.Faelle.Schleifen.Counters.CounterCall
@[expose] public section


namespace Gabbro.Stage0.Senke.CounterCallProbe
open Gabbro.Grammatik Runner.IR Runner.Mem FnptrProben
set_option maxRecDepth 2000

local instance (m : Runner.Mem) (pc : Runner.W) (o : Nat) (a b c : BitVec 32) :
    Decidable (InsAt m pc o a b c) :=
  if h : m.rd8 pc = some (BitVec.ofNat 8 o) ∧ m.rd32 (pc + 4) = some a ∧
      m.rd32 (pc + 8) = some b ∧ m.rd32 (pc + 12) = some c then
    .isTrue ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  else .isFalse (fun h' => h ⟨h'.op, h'.f1, h'.f2, h'.f3⟩)

theorem image_far : CodeFar 2016 image.length 4096 256 := by
  unfold CodeFar; decide +kernel

theorem loaded_header [Kern] (b : Fin 3) : Header b.val (loaded b) := by
  refine ⟨loaded_pre b, loaded_surroundings b, loaded_head b, loaded_world b,
    ?_, counter_values b, ?_, sentinel_values b⟩
  · have h : ∀ b : Fin 3, ∀ k : Fin image.length,
        InsAt (loaded b) (2016 + BitVec.ofNat 64 (16 * k.val))
          image[k.val].o (II.f image[k.val].a) (II.f image[k.val].b) (II.f image[k.val].c) := by
      apply allFin; decide +kernel
    exact fun k hk => h b ⟨k, hk⟩
  · have h : ∀ b : Fin 3, (loaded b).rd64 (slot 4096 5) = some 1 := by
      apply allFin; decide +kernel
    exact h b

/-- One actual iteration returns every interface needed by the next iteration.
    No equality with a reset fixture memory is used. -/
theorem header_step [Kern] {n : Nat} {m : Runner.Mem}
    (h : Header (n + 1) m) (fits : n + 1 < 2 ^ 64) :
    ∃ m', Star ⟨2016, 4096⟩ m ⟨2016, 4096⟩ m' ∧ Header n m' := by
  let m1 := write m (slot 4096 6) 8 (BitVec.ofNat 64 n).toNat
  have a : Agree (4096 : Runner.W) 4 256 m m1 :=
    agree_write h.pre.frame.room (by decide) (by decide) _
  have aw : AgreeW callLayout 4096 4 256 m m1 := agreeW_of a
  have hp : PreS callLayout m1 2048 4096 256 8 code (Env.nil : Env D []) 4 :=
    ⟨h.pre.ctx, h.pre.small, frameOK_agreeW h.pre.frame aw,
      codeAt_agreeWIn call_win aw h.pre.code h.pre.far, h.pre.far,
      (fun _ x => nomatch x), trivial, wstab_true _ _⟩
  have hw : WeltAt m1 callLayout world := weltAt_stab call_win.lay call_win.top m m1 h.world (a.mono (Nat.zero_le _))
  have im1 := codeAt_agreeWIn call_win aw h.image image_far
  have test := h.image 0 (by decide +kernel)
  have dec := h.image 1 (by decide +kernel)
  have edge := im1 (code.length + 2) (by decide +kernel)
  change InsAt m 2016 19 6 (II.f (16 * (code.length + 3 : Nat))) 0 at test
  change InsAt m 2032 4 6 6 5 at dec
  change InsAt m1 (2048 + BitVec.ofNat 64 (16 * code.length)) 18
    (II.f (-(16 * (code.length + 2 : Nat)))) 0 0 at edge
  have wr : m.wr64 (slot 4096 6) (BitVec.ofNat 64 (n + 1) - 1) = some m1 := by
    rw [(counter_fuel_step n fits).2]
    exact wr64_some (h.pre.frame.wr 6 (by decide))
  have start := Star.one (counter_positive (t := ⟨2016, 4096⟩) test h.count
    (counter_fuel_step n fits).1)
  have down := Star.one (counter_decrement (t := ⟨2032, 4096⟩) dec h.count h.unit wr)
  have stored : m1.rd64 (slot 4096 6) = some (BitVec.ofNat 64 n) :=
    rd64_write_same (h.pre.frame.rd 6 (by decide))
  obtain ⟨m', run, frame, _, world', kept, count⟩ := Reach.counter_backedge
    (body_simulation_at hp (h.surround.agreeW call_win aw (by decide))
      (h.head.agreeW call_win aw (by decide)) hw)
    call_win (counter := 6) (Or.inr (by simp)) (by decide) stored edge
    (by unfold CodeFar; decide +kernel)
  have all := aw.trans frame
  refine ⟨m', start.trans (down.trans ?_), ?_⟩
  · have target : (2048 : Runner.W) + BitVec.ofNat 64 (16 * code.length) +
        sx (II.f (-(16 * (code.length + 2 : Nat)))) = 2016 := by decide +kernel
    have next : Runner.IR.nxt ⟨2032, 4096⟩ = ⟨2048, 4096⟩ := by decide +kernel
    rw [next]
    simpa only [target] using run
  · refine ⟨?_, h.surround.agreeW call_win all (by decide),
      h.head.agreeW call_win all (by decide), world',
      codeAt_agreeWIn call_win all h.image image_far, count, ?_, ?_⟩
    · exact ⟨h.pre.ctx, h.pre.small, frameOK_agreeW h.pre.frame all,
        codeAt_agreeWIn call_win all h.pre.code h.pre.far, h.pre.far,
        (fun _ x => nomatch x), trivial, wstab_true _ _⟩
    · change m'.rd64 (slot 4096 (BitVec.ofNat 64 5)) = some 1
      rw [kept 5 (by simp)]
      exact (keeps_write (K := 256) h.pre.frame.room (by decide)
        (pr := [4, 5]) (by intro j hj; simp at hj; rcases hj with rfl | rfl <;> decide)
        (by decide) _ 5 (by simp)).trans h.unit
    · change m'.rd64 (slot 4096 (BitVec.ofNat 64 4)) = some 77
      rw [kept 4 (by simp)]
      exact (keeps_write (K := 256) h.pre.frame.room (by decide)
        (pr := [4, 5]) (by intro j hj; simp at hj; rcases hj with rfl | rfl <;> decide)
        (by decide) _ 4 (by simp)).trans h.sentinel

/-- The actual zero branch and exit bytes work in the memory left by all passes. -/
theorem header_stop [Kern] {m : Runner.Mem} (h : Header 0 m) :
    Stops ⟨2016, 4096⟩ m 111 := by
  have test := h.image 0 (by decide +kernel)
  change InsAt m 2016 19 6 (II.f (16 * (code.length + 3 : Nat))) 0 at test
  apply counter_budget_stop_code test h.count (K := 256) (scratch := 8)
  · have hc := codeAt_right (show CodeAt m 2016
        (([ci 19 6 (16 * (code.length + 3 : Nat)) 0, ci 4 6 6 5] ++
          code ++ [ci 18 (-(16 * (code.length + 2 : Nat))) 0 0]) ++ stopC 111 8) from h.image)
    have eq : (2016 : Runner.W) + BitVec.ofNat 64
        (16 * ([ci 19 6 (16 * (code.length + 3 : Nat)) 0, ci 4 6 6 5] ++
          code ++ [ci 18 (-(16 * (code.length + 2 : Nat))) 0 0]).length) =
        2016 + sx (II.f (16 * (code.length + 3 : Nat))) := by decide +kernel
    rw [eq] at hc
    exact hc
  · unfold CodeFar; decide +kernel
  · exact h.pre.frame
  · decide
  · decide

/-- Every requested prefix consumes exactly that many budget units. The
    successor proof executes one test, decrement, emitted body and backedge;
    neither the code image nor its size depends on the prefix length. -/
theorem counted_prefix [Kern] (remaining iterations : Nat)
    (fits : remaining + iterations < 2 ^ 64) (m : Runner.Mem)
    (h : Header (remaining + iterations) m) :
    ∃ m', Star ⟨2016, 4096⟩ m ⟨2016, 4096⟩ m' ∧ Header remaining m' := by
  induction iterations generalizing m with
  | zero => exact ⟨m, Star.refl _ _, h⟩
  | succ k ih =>
    obtain ⟨m1, step, entry⟩ := header_step h fits
    obtain ⟨m2, rest, final⟩ := ih (by omega) m1 entry
    exact ⟨m2, step.trans rest, final⟩

/-- Induction executes the same emitted loop until exhaustion. Each successor
    consumes exactly one natural budget unit by `header_step`; its body is the
    generic lowering theorem for the real store and reachable call. -/
theorem counted_exhaustion [Kern] (n : Nat) (fits : n < 2 ^ 64)
    (m : Runner.Mem) (h : Header n m) :
    ∃ m', Star ⟨2016, 4096⟩ m ⟨2016, 4096⟩ m' ∧ Header 0 m' ∧
      Stops ⟨2016, 4096⟩ m' 111 := by
  induction n generalizing m with
  | zero => exact ⟨m, Star.refl _ _, h, header_stop h⟩
  | succ n ih =>
    obtain ⟨m1, step, entry⟩ := header_step h fits
    obtain ⟨m2, rest, final, stop⟩ := ih (by omega) m1 entry
    exact ⟨m2, step.trans rest, final, stop⟩

/-- Joint end-to-end witnesses for budgets zero, one and two. The final header
    retains the sentinel, immutable unit, zero counter, frame, code and callees. -/
theorem counted_exhaustion_zeuge [Kern] (b : Fin 3) :
    Stops ⟨2016, 4096⟩ (loaded b) 111 ∧
    ∃ m', Star ⟨2016, 4096⟩ (loaded b) ⟨2016, 4096⟩ m' ∧ Header 0 m' := by
  obtain ⟨m', run, final, stop⟩ := counted_exhaustion b.val
    (by have := b.isLt; omega) (loaded b) (loaded_header b)
  exact ⟨Stops.prefix run stop, m', run, final⟩

/-- The actual source body falls through. Its semantic access trace is
    retained in the resulting world, rather than reset between iterations. -/
theorem source_body (σ : World D) :
    ∃ σ', execBlock O 1 (rufAt tiny O 1 2) (body true)
      σ (Env.nil : Env D []) = .ok σ' Env.nil := by
  exact ⟨_, rfl⟩

/-- Canonical repetition of the actual source body exhausts its natural fuel. -/
theorem source_exhaustion (n : Nat) (σ : World D) :
    foreverLauf (l := false) (() : D.Annahme)
      (fun σ ρ => execBlock O 1 (rufAt tiny O 1 2) (body true) σ ρ)
      (fun σ _ => (σ, true)) n σ (Env.nil : Env D []) =
      .hardware (.fortschritt ()) := by
  induction n generalizing σ with
  | zero => rfl
  | succ n ih =>
    obtain ⟨σ', hb⟩ := source_body σ
    simp only [foreverLauf, Bool.true_eq_false, ite_false, hb]
    exact ih σ'

/-- The canonical source outcome is realized by the counted actual image.
    This separate counter image retains its direct Runner witness alongside
    the now accepted generic whole-loop lowering. -/
theorem source_counted_zeuge [Kern] (b : Fin 3) :
    Sim callLayout tiny 2 world Env.nil 0 0 4096 4 256 [4, 5, 6]
      ⟨2016, 4096⟩ (loaded b) 0 0 0
      (foreverLauf (l := false) (() : D.Annahme)
        (fun σ ρ => execBlock O 1 (rufAt tiny O 1 2) (body true) σ ρ)
        (fun σ _ => (σ, true)) b.val world (Env.nil : Env D [])) 4 := by
  rw [source_exhaustion]
  exact (counted_exhaustion_zeuge b).1

end Gabbro.Stage0.Senke.CounterCallProbe
