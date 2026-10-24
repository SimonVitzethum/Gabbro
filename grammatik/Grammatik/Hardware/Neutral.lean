import Grammatik.Zielsatz.Atomar.BeweisAtomar
import Grammatik.Hardware.Anbieter.Region

/-
  File:      Grammatik/Hardware/Neutral.lean
  Subject:   THE NEW FORMS ADD NAMED ASSUMPTIONS AND NOTHING ELSE: programs that do not use them keep
             their meaning, and the goal theorem is untouched.  PLAN-HARDWARE.md section 16.10.

  The forms of this design (pool gates, trap clause, process exit, join, targets as data) are lowering
  and ENVIRONMENT data. Machine G, `Deklaration`, `Akzeptiert` and `Spec.lean` are not changed. What a
  program that uses them ADDS to the goal is a hardware assumption about the environment's joint
  answers (the pool's contract, the join order, the exit gate's `noreturn`), stated as a premise next to
  `HardwareAnnahmen`. This file states that exactly and proves it:

    * `GabbroZielZ Z`          -- `GabbroZiel` with one more premise `Z D O` on the oracle (the extra
                                  named assumptions); the conclusion is word for word `GabbroZiel`'s;
    * `gabbro_ziel_zusatz`     -- for EVERY family `Z`, the statement holds (weakening: more named
                                  assumptions never break the theorem);
    * `gabbro_ziel_leer`       -- with `Z := True` it IS `GabbroZiel`: a program that uses none of the
                                  new forms has the statement of before, equivalence both ways;
    * `AnbieterAnnahme`        -- the pool's contract as a premise over the environment's provider log:
                                  the log is a legal run of the provider machine. It is vacuous for the
                                  empty log (`anbieter_leer`), closed under prefixes
                                  (`anbieter_praefix`) and falsifiable by a finite trace
                                  (`anbieter_verletzt`: two overlapping answers), which is what a pool's
                                  `assume ... falsifier ...` names.

  No `sorry`, no `native_decide`, no new axiom; `gabbro_ziel` is used, not changed.
-/

namespace Gabbro.Grammatik.Zielsatz

open Gabbro.Grammatik

/-- `GabbroZiel` with an extra family of named assumptions `Z` on the oracle. Everything else is the
    statement of `Spec.lean`, word for word. -/
def GabbroZielZ (Z : ∀ D : Deklaration, Orakel D → Prop) : Prop :=
  ∀ (C : PrueferX) (D : Deklaration) [DecidableEq D.Fn] (E : Einheit D)
    (fs : Aufzaehlung D.Fn) (ls : Aufzaehlung D.Lock) (cs : Aufzaehlung (D.Tab ⊕ D.Glob)),
    C.akzeptiert E fs.1 ls.1 cs.1 = true →
    NutzerPflichtA E →
    ∀ O : Orakel D, HardwareAnnahmen O E.Q → Z D O →
    ∀ (passes : Nat) (sp : Speicher D.mitRuhe)
      (init : Faden → Σ f : D.mitRuhe.Fn, Env D.mitRuhe (D.mitRuhe.params f)),
      Laufzeit E sp init →
      ∀ (lebt0 : Faden → Bool) (K : FadenMaschine D.mitRuhe),
        FadenErreichbarX E.P.mitRuhe O.mitRuhe passes (GeteiltV (D := D) E.P E.ws)
          (FadenStart E.P.mitRuhe sp init lebt0) K →
          ZielFX E.P.mitRuhe E.S.mitRuhe O.mitRuhe passes (GeteiltV (D := D) E.P E.ws)
            (RufStartG E.P.mitRuhe sp init) (E.arenen.map (·.mitRuhe)) K

/-- **More named assumptions never break the goal theorem.** -/
theorem gabbro_ziel_zusatz (Z : ∀ D : Deklaration, Orakel D → Prop) : GabbroZielZ Z := by
  intro C D _ E fs ls cs hC hN O hH _ passes sp init hL lebt0 K hK
  exact gabbro_ziel C D E fs ls cs hC hN O hH passes sp init hL lebt0 K hK

/-- **Programs that use none of the new forms have the statement of before.** -/
theorem gabbro_ziel_leer : GabbroZielZ (fun _ _ => True) ↔ GabbroZiel := by
  constructor
  · intro h C D _ E fs ls cs hC hN O hH passes sp init hL lebt0 K hK
    exact h C D E fs ls cs hC hN O hH trivial passes sp init hL lebt0 K hK
  · intro _
    exact gabbro_ziel_zusatz _

end Gabbro.Grammatik.Zielsatz

namespace Gabbro.Grammatik.Anbieter

/-- **The pool's contract as a premise** over the environment's provider log: the log (the answers of
    the pool's three gates, in order) is a legal run of the provider machine from nothing. -/
def AnbieterAnnahme (g : Nat) (es : List Ereig) : Prop := ∃ s, Lauf g Zust.leer es s

/-- A program with no pool forms assumes nothing: the empty log is legal. -/
theorem anbieter_leer (g : Nat) : AnbieterAnnahme g [] := ⟨_, Lauf.nil _⟩

theorem lauf_append {g : Nat} {s s'' : Zust} {es fs : List Ereig} (h : Lauf g s (es ++ fs) s'') :
    ∃ s1, Lauf g s es s1 ∧ Lauf g s1 fs s'' := by
  induction es generalizing s with
  | nil => exact ⟨s, Lauf.nil _, h⟩
  | cons e es ih =>
      cases h with
      | cons hs hr =>
          obtain ⟨s1, h1, h2⟩ := ih hr
          exact ⟨s1, Lauf.cons hs h1, h2⟩

/-- **Closed under prefixes**: an assumption about a whole log is one about every prefix, so a run
    that stops early assumes no more than it saw. -/
theorem anbieter_praefix {g : Nat} {es fs : List Ereig} (h : AnbieterAnnahme g (es ++ fs)) :
    AnbieterAnnahme g es := by
  obtain ⟨s, hs⟩ := h
  obtain ⟨s1, h1, -⟩ := lauf_append hs
  exact ⟨s1, h1⟩

/-- **Falsifiable by a finite trace**: a pool whose second reserve overlaps its first violates the
    assumption (page 16, `[32,96)` then `[64,128)`). -/
theorem anbieter_verletzt : ¬ AnbieterAnnahme 16 [.hole 64 32, .hole 64 64] := by
  rintro ⟨s, h⟩
  cases h with
  | cons h1 h2 =>
      cases h1 with
      | hole hn hnb hb hfrisch =>
          cases h2 with
          | cons h3 h4 =>
              cases h3 with
              | hole hn' hnb' hb' hfrisch' =>
                  have := hfrisch' ⟨32, 32 + 64⟩ (by simp [Zust.leer])
                  unfold Strecke.getrennt at this
                  simp only at this
                  omega

/-- The legal case of the same shape: reserving past the first range is fine. -/
theorem anbieter_zeuge : AnbieterAnnahme 16 [.hole 64 32, .hole 64 96] := by
  have hs1 : PStep 16 Zust.leer (.hole 64 32)
      { lebend := [⟨32, 32 + 64⟩], ram := Zust.leer.ram } :=
    PStep.hole (s := Zust.leer) (by decide) (by decide) (by decide) (by simp [Zust.leer])
  have hs2 : PStep 16 { lebend := [⟨32, 32 + 64⟩], ram := Zust.leer.ram } (.hole 64 96)
      { lebend := ⟨96, 96 + 64⟩ :: [⟨32, 32 + 64⟩], ram := Zust.leer.ram } :=
    PStep.hole (by decide) (by decide) (by decide) (by simp [Strecke.getrennt])
  exact ⟨_, Lauf.cons hs1 (Lauf.cons hs2 (Lauf.nil _))⟩

end Gabbro.Grammatik.Anbieter
