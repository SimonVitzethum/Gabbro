/-
  File:      stage0/Stage0/Senke/Bild/Mehr/SC.lean
  Subject:   The runner's sequentially consistent memory model answers like the memory (multi-thread image theorem,
             package MT1). `Runner.Beweis.SC L` answers a write and a compare-and-swap exactly as `memAns` does
             (`sc_memAns_wr`, `sc_memAns_cas`), and a read of one, four or eight bytes as `memAns` does up to the
             second word of the answer, which a read leaves free (`sc_memAns_rd`: with that word zero, the answers
             are equal). That the instructions' read continuations ignore the second word is the `Blind` property of
             package MT2; with it every step of the IR process over `SC L` that the memory answers is an `MSchritt`.
-/
module
public import Runner.Mach.Folge
public import Stage0.Senke.Bild.Mehr.Lokal
@[expose] public section

namespace Gabbro.Stage0.Senke.BildMehr

open Runner Runner.IR Runner.Beweis

/-- A write: the model's answer is the memory's. -/
theorem sc_memAns_wr {L : Lay} {s s' : (SC L).St} {i : Nat} {x v : W} {a : Ans}
    (h : (SC L).ans s i (.wr x v) a s') : memAns s.1 (.wr x v) = some (a, s'.1) := by
  rcases h with ⟨hw, rfl, rfl⟩ | ⟨m, hw, rfl, hm⟩
  · simp only [memAns_wr, hw]
  · simp only [memAns_wr, hw, hm]

/-- A compare-and-swap: the model's answer is the memory's. -/
theorem sc_memAns_cas {L : Lay} {s s' : (SC L).St} {i : Nat} {x e n : W} {a : Ans}
    (h : (SC L).ans s i (.cas x e n) a s') : memAns s.1 (.cas x e n) = some (a, s'.1) := by
  rcases h with ⟨hc, rfl, rfl⟩ | ⟨old, m, hc, rfl, hm⟩
  · simp only [memAns_cas, hc]
  · simp only [memAns_cas, hc, hm]

/-- A read of one, four or eight bytes whose second answer word is zero: the model's answer is the memory's. -/
theorem sc_memAns_rd {L : Lay} {s s' : (SC L).St} {i n : Nat} {x : W} {a : Ans}
    (h : (SC L).ans s i (.rd n x) a s') (hn : n = 1 ∨ n = 4 ∨ n = 8) (h0 : ∀ v w, a = some (v, w) → w = 0) :
    memAns s.1 (.rd n x) = some (a, s'.1) := by
  obtain ⟨hs, w, ha⟩ := h
  subst s'
  subst a
  rcases hn with rfl | rfl | rfl
  · cases hr : s.1.rd8 x with
    | none => simp [memAns, rdN, hr]
    | some b =>
      have hw := h0 (b.setWidth 64) w (by simp [rdN, hr])
      subst hw
      simp [memAns, rdN, hr]
  · cases hr : s.1.rd32 x with
    | none => simp [memAns, rdN, hr]
    | some b =>
      have hw := h0 (b.setWidth 64) w (by simp [rdN, hr])
      subst hw
      simp [memAns, rdN, hr]
  · cases hr : s.1.rd64 x with
    | none => simp [memAns, rdN, hr]
    | some b =>
      have hw := h0 b w (by simp [rdN, hr])
      subst hw
      simp [memAns, rdN, hr]

/-- The memory answer of a generated request is a valid SC answer
    on the same bytes. A write or CAS preserves the dispatch table,
    and a read takes the allowed zero auxiliary word. -/
theorem memAns_sc {L : Lay} {s : (SC L).St} {i : Nat}
    {request : Op} {a : Ans} {after : Mem}
    (width : ∀ n x, request = .rd n x → n = 1 ∨ n = 4 ∨ n = 8)
    (answer : memAns s.1 request = some (a, after)) :
    ∃ invariant : TabInv L after, (SC L).ans s i request a ⟨after, invariant⟩ := by
  cases request with
  | rd n address =>
    obtain rfl | rfl | rfl := width n address rfl <;>
      simp only [memAns, Option.some.injEq, Prod.mk.injEq] at answer <;>
      obtain ⟨rfl, rfl⟩ := answer
    all_goals
      refine ⟨s.2, rfl, 0, ?_⟩
      simp only [rdN, Option.map_map, Function.comp_def]
  | wr address value =>
    cases written : s.1.wr64 address value <;>
      simp only [memAns_wr, written, Option.some.injEq, Prod.mk.injEq] at answer <;>
      obtain ⟨rfl, rfl⟩ := answer
    · exact ⟨s.2, .inl ⟨written, rfl, rfl⟩⟩
    · exact ⟨s.2.keep (wr64_keeps written), .inr ⟨_, written, rfl, rfl⟩⟩
  | cas address expected value =>
    cases compared : s.1.cas address expected value with
    | none =>
      simp only [memAns_cas, compared, Option.some.injEq, Prod.mk.injEq] at answer
      obtain ⟨rfl, rfl⟩ := answer
      exact ⟨s.2, .inl ⟨compared, rfl, rfl⟩⟩
    | some returned =>
      rcases returned with ⟨old, changed⟩
      simp only [memAns_cas, compared, Option.some.injEq, Prod.mk.injEq] at answer
      obtain ⟨rfl, rfl⟩ := answer
      exact ⟨s.2.keep (cas_keeps compared), .inr ⟨_, _, compared, rfl, rfl⟩⟩
  | fp | sys => cases answer

end Gabbro.Stage0.Senke.BildMehr
