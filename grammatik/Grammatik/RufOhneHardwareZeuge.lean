/-
  File:      Grammatik/RufOhneHardwareZeuge.lean
  Subject:   WITNESSES for `RufOhneHardware.lean`, both ways:

  * THE FINDING (`befund_hardware_bleibt`). The checker's Bool and the user's
    duty do NOT rule out a `hardware` outcome of `rufAt`, and premise (c)
    `HardwareAnnahmen` does not either. The shape is named and built: an
    AXIOM CALL whose raw answer misses its declared result type. On the
    witness program `axP` of `AxiomVertrag.lean` -- which is in the checker's
    fragment (`programmImFragmentV`), passes the footprint check, and whose
    every function meets the user's obligation `KoerperGutA` AGAINST EVERY
    ORACLE in the premise class -- the oracle `axOBoese` meets all three legs
    of `HardwareAnnahmen` (`GutO`, `RegLokal`, `AxVertragO`) and the call
    `zaehle` still ends in `.hardware (.annahme inc)` at every depth.
    `AxVertragO` is met VACUOUSLY, and that is the whole point: the declared
    axiom ensures constrains the oracle only WHERE its raw answer fits the
    declared type, so an answer that does not fit is admitted by the
    premise and stops the model.

  * THE DISCHARGE (`ohneHardware_zeuge`). The same program with an oracle
    whose answer does fit is NOT what saves it -- `axP`'s body carries the
    form, so the check refuses it (`hardwareFrei = false`). What saves a
    chain is the ABSENCE of the form: `korrOk` refuses every one of the five,
    and the discharge is exercised on a body that really runs
    (`ohneHardware_zeuge`: `haupt`'s body has the check, calls `zaehle`, and
    the handler premise is what carries the call).
-/
import Grammatik.RufOhneHardware
import Grammatik.ZielOrtAxZeuge
import Grammatik.Zielsatz.Spec
import Grammatik.CFormenM

namespace Gabbro.Grammatik

open Zielsatz

/-! ## 1. The oracle that meets every hardware assumption and still stops -/

/-- **The oracle of the finding**: `axO`'s world effect (so every clause of
    `GutO`, which speaks about the answer WORLD, is `axO`'s), with a raw
    answer of `99` -- outside `inc`'s declared result type `int 0 3`. -/
def axOBoese : Orakel axD :=
  { axO with wirkt := fun a σ ρ => ((axO.wirkt a σ ρ).1, 99) }

/-- The answer world is `axO`'s, so the frame and trace clauses are. -/
theorem axOBoese_gut : GutO axOBoese := axO_gut

theorem axOBoese_reglokal : RegLokal axOBoese :=
  ⟨(fun r => nomatch r), (fun g => nomatch g)⟩

/-- `99` does not fit `inc`'s declared result type -- so the axiom's answer
    at every world and every argument list is `none`. -/
theorem axOBoese_passt_nicht (a : axD.Ax) (σ : World axD) (ρ : Env axD (axD.aparams a)) :
    einpassenErg axOBoese.zeiger (axD.aerg a) (axOBoese.wirkt a σ ρ).2 = none := by
  show einpassen axOBoese.zeiger (.int 0 3) (99 : Int) = none
  simp only [einpassen, dif_neg (show ¬ ((0 : Int) ≤ 99 ∧ (99 : Int) ≤ 3) by decide)]

/-- **The declared axiom ensures is MET -- vacuously.** `AxVertragO` asks
    something only where the raw answer fits the declared type, and this one
    never does. Premise (c) of the goal theorem therefore holds. -/
theorem axOBoese_vertrag : AxVertragO axQ axOBoese := by
  intro a σ ρ v hv
  rw [axOBoese_passt_nicht a σ ρ] at hv
  cases hv

theorem axOBoese_hardware : HardwareAnnahmen axOBoese axQ :=
  ⟨axOBoese_gut, axOBoese_reglokal, axOBoese_vertrag⟩

/-- The axiom's answer at any world: the world is `axO`'s, the value is none. -/
theorem axOBoese_antwort (σ : World axD) :
    axiomAntwort axOBoese axInc σ .nil = ((axO.wirkt axInc σ .nil).1, none) := by
  show ((axOBoese.wirkt axInc σ .nil).1,
    einpassenErg axOBoese.zeiger (axD.aerg axInc) (axOBoese.wirkt axInc σ .nil).2) = _
  rw [axOBoese_passt_nicht axInc σ .nil]
  rfl

/-- `zaehle`'s body, against this oracle and ANY handler, stops at the
    hardware assumption. -/
theorem axOBoese_lauf (passes : Nat)
    (R : ∀ f : axD.Fn, World axD → Env axD (axD.params f) → RufAusgang f) (σ : World axD) :
    execEnd axOBoese passes R (axP.rumpf axZaehle) σ .nil = .hardware (.annahme axInc) :=
  axZaehle_lauf axEnsInc axOBoese passes R σ _ none (axOBoese_antwort _)

/-- **And so does the CALL, at every depth above `0` and every budget.** -/
theorem axOBoese_rufAt (passes n : Nat) (σ : World axD) :
    rufAt axP axOBoese passes (n + 1) axZaehle σ .nil = .hardware (.annahme axInc) :=
  rufAt_hardware_von_rumpf axP axOBoese passes n axZaehle σ .nil _ rfl (axOBoese_lauf _ _ _)

/-- **THE FINDING.** Every premise the goal theorem has about the checker's
    program facts, about the user's logic and about the hardware holds, and
    the model's call still ends in an error -- the one error class the
    premises do not speak about. The shape is the axiom call; the reason is
    that `AxVertragO` is conditional on the answer fitting. The check of
    `RufOhneHardware.lean` sees the shape (`hardwareFrei = false`), and so
    does the certificate check, which has no row for it at all. -/
theorem befund_hardware_bleibt :
    -- the checker's fragment admits the body, and the footprint checks
    programmImFragmentV axP axFs = true ∧ fussOrtB axP axFs = true ∧
    -- the user's duty holds for every function, against EVERY oracle in the
    -- premise class -- so it holds against `axOBoese` too
    (∀ f : axD.Fn, KoerperGutA axP 0 axQ f) ∧
    -- the hardware assumptions (c) hold of `axOBoese`
    HardwareAnnahmen axOBoese axQ ∧
    -- and the call ends in a model error at every depth and every budget
    (∀ (passes n : Nat) (σ : World axD),
      rufAt axP axOBoese passes (n + 1) axZaehle σ .nil = .hardware (.annahme axInc)) ∧
    (∀ (passes n : Nat) (σ : World axD),
      (rufAt axP axOBoese passes (n + 1) axZaehle σ .nil).istFehler = true) ∧
    -- the syntactic check sees the shape
    (axP.rumpf axZaehle).hardwareFrei = false :=
  ⟨axP_fragment, axP_fuss, axP_koerperA, axOBoese_hardware, axOBoese_rufAt,
    fun passes n σ => by rw [axOBoese_rufAt]; rfl, rfl⟩

/-! ## 2. The discharge, on a body that really runs -/

/-- `ruhe`'s body carries no oracle form; `zaehle`'s and `haupt`'s do (the
    axiom sits in `zaehle`, and `haupt` reaches it only through a call --
    the check is SYNTACTIC per body, and `haupt`'s own body is clean). -/
theorem axHaupt_hardwareFrei : (axP.rumpf axHaupt).hardwareFrei = true := rfl

theorem axRuhe_hardwareFrei : (axP.rumpf axRuhe).hardwareFrei = true := rfl

/-- **The check is per body, and the handler premise carries the call.**
    `haupt`'s body is clean, and still its run can end in a hardware outcome
    -- through the CALL of `zaehle`, whose body is not. That is exactly why
    `Endblock.hardwareFrei_ok` takes `OhneHardware R`, and why
    `rufAt_ohneHardware` asks the check of EVERY body. -/
theorem ohneHardware_zeuge :
    (axP.rumpf axHaupt).hardwareFrei = true ∧
    ¬ (∀ f : axD.Fn, (axP.rumpf f).hardwareFrei = true) ∧
    (∀ (passes n : Nat) (σ : World axD),
      rufAt axP axOBoese passes (n + 2) axHaupt σ .nil = .hardware (.annahme axInc)) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro h
    have hz : (false : Bool) = true := h axZaehle
    cases hz
  intro passes n σ
  have hb : execEnd axOBoese passes (rufAt axP axOBoese passes (n + 1)) (axP.rumpf axHaupt)
      (σ.lese (Signatur.anfang axD (axD.signatur axHaupt)) (axP.requires axHaupt).orte) .nil =
      .hardware (.annahme axInc) := by
    show execEnd axOBoese passes (rufAt axP axOBoese passes (n + 1)) axRumpfHaupt _ .nil = _
    simp only [axRumpfHaupt, axRufZaehle, execEnd, execStmt, Args.orte, evalArgs,
      axOBoese_rufAt passes n]
    rfl
  exact rufAt_hardware_von_rumpf axP axOBoese passes (n + 1) axHaupt σ .nil _ rfl hb

#print axioms Gabbro.Grammatik.axOBoese_gut
#print axioms Gabbro.Grammatik.axOBoese_vertrag
#print axioms Gabbro.Grammatik.befund_hardware_bleibt
#print axioms Gabbro.Grammatik.ohneHardware_zeuge

end Gabbro.Grammatik
