module

public import Gabbro.Body
public import Gabbro.Coverage.Teil3

@[expose] public section

namespace Gabbro.Coverage
open Gabbro.Body

theorem every_assumption_has_a_name :
    ∀ (f : Form) (n : String), classify f = .assumed n → n ≠ "" := by
  intro f n h
  cases f
  case refusedOrAssumed r =>
    cases r <;> simp_all [classify, Reason.kind, Reason.tag] <;> simp only [← h, String.reduceEq, not_false_eq_true]
  case initialState => simp only [classify] at h; cases h; simp only [ne_eq, String.reduceEq, not_false_eq_true]
  case environmentRunsBody => simp only [classify] at h; cases h; simp only [ne_eq, String.reduceEq, not_false_eq_true]
  case environmentRunsLoop => simp only [classify] at h; cases h; simp only [ne_eq, String.reduceEq, not_false_eq_true]
  case environmentBoundsPasses => simp only [classify] at h; cases h; simp only [ne_eq, String.reduceEq, not_false_eq_true]
  case distinctCarriers => simp only [classify] at h; cases h; simp only [ne_eq, String.reduceEq, not_false_eq_true]
  case checkerAndEmitterTrusted => simp only [classify] at h; cases h; simp only [ne_eq, String.reduceEq, not_false_eq_true]
  all_goals simp only [classify, reduceCtorEq] at h

/-- ## The sentence the plan serves, as a proposition

    **For every form of this grammar that is not the person's own logic, the channel
    answers**: a general lemma carries it, the automation closes it on the corpus, it is
    assumed under a name, or it is refused under a tag. Nothing falls through, and nothing
    that the language fixes is handed over in silence. -/
theorem the_sentence : ∀ f : Form, ¬ IsOwnLogic f →
    classify f = .carried ∨ classify f = .carriedByTactic ∨
    (∃ n, classify f = .assumed n) ∨ (∃ t, classify f = .refused t) := by
  intro f h
  cases hv : classify f with
  | carried => exact Or.inl rfl
  | carriedByTactic => exact Or.inr (Or.inl rfl)
  | assumed n => exact Or.inr (Or.inr (Or.inl ⟨n, rfl⟩))
  | refused t => exact Or.inr (Or.inr (Or.inr ⟨t, rfl⟩))
  | ownLogic => exact absurd (ownLogic_is_the_persons f hv) h
  | unhandled => exact absurd hv (classify_total f)

/-! ## 7. What this file does NOT prove -- read this beside section 6

    1. **That `gabbro_auto` closes anything.** `Form.arithmeticBounds` and `Form.budget`
       are `carriedByTactic`, `Discharges` is `False` for both, and the corpus is the only
       evidence there is for them.
    2. **That `Form` is the whole grammar.** It is a hand-written mirror; the guard
       `instrumente/pruefe-deckung.py` holds the `Reason` half against `lean.rs` line for
       line, and the rest of the enumeration against the emitter's carried decision points
       only as far as the code names them. What it cannot check is written in its header.
    3. **That the emitter writes the statements these lemmas assume.** Every proposition
       above is about the MODEL. That the emitter's `_pre`/`_post`/`_inv` say what the
       person's `.gab` file says is the emitter's correctness, and `PLAN.md` section 1 puts
       it explicitly out of scope: the checker and the emitter are trusted, not verified
       (`Form.checkerAndEmitterTrusted`).
    4. **That a form which MEANS NOTHING is caught.**
       `messung/GRAMMATIK-VOLLSTAENDIG-2026-09-08.md` section 1 measures four forms the
       checker admits and that have no effect. This file answers that document's point 2
       (the proof channel answers for every form) and says nothing about its points 1 and 3.

       *Its section 1.1 -- the quantifier domain as decoration -- has since been closed on
       the CHECKER's side and not on this one*: `D022` refuses a binder used against its
       domain, `D023` hints where the body never mentions it, and `D024` refuses the last
       green form of `threads` (`PLAN.md` section 15). **That is a change to what the
       grammar admits, and it makes no verdict of this file different** -- a form the
       checker now rejects raises no obligation, and a refusal that stands cannot become
       weaker for it.
-/

end Gabbro.Coverage
