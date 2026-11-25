module

public import Core.Ast.LowLevel.DeviceUnit
public import Core.Beobachtung.Satz
public import Core.Beobachtung.Fluss.Beweise.Geraet

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine
open Gabbro.Core.Ast.LowLevel.Device (RegisterAccess State)

/- Design note (geraet-ni): `RegelFluss` alone does not force the right run into the
   same step kind. A consume step is silent while an answer arrival appends two low
   events (`geraete_issue_beob`, `geraete_antwort_beob`), so an arrival-vs-consume
   interleaving breaks prefix-length equality of the coupling. The missing duty is
   the pinned `GeraeteProtokollNIAussage` (`ProtokollNIPflicht` with `PausenNIPflicht`
   for the device unit, in the language of `Satz.lean`), together with a
   question/history equality invariant below.

   The semantic duty quantifies over all runs and comparisons, so it is not itself
   a decidable checker line. The `Bool` rule below is the decidable checker line on
   the device syntax: it accepts exactly the elaborated shapes (`registerRule` with
   no phase target, `transitionRule` with a free phase target). The open prover
   step is: `RegelFluss` plus this rule (and the invariant) give
   `GeraeteProtokollNIAussage`, hence `GeraeteNIAussage` unchanged. -/

/-- The question/history equality invariant for two device states: the pending
    question ledgers agree, the outside histories agree, and every context's frame
    agrees on its pending question. From coupled states with equal offers both
    sides then enable the same step kind (issue needs `pending = none`, consume
    and arrival need `pending = some`), so arrival-vs-consume interleavings cannot
    start. -/
def geraetFragenVerlaufGleich (v u : State) : Prop :=
  v.fragen = u.fragen ∧ v.verlauf = u.verlauf ∧
    ∀ c, (v.lokal c).pending = (u.lokal c).pending

/-- The invariant is satisfiable: every state is equal to itself. -/
theorem geraetFragenVerlaufGleich_refl (v : State) : geraetFragenVerlaufGleich v v :=
  ⟨rfl, rfl, fun _ => rfl⟩

/-- The decidable checker line on the device syntax: register steps keep no phase
    target, transitions move only between the free phases `ready` and `reset`.
    A `Bool` function, so the checker decides it without any user obligation. -/
def geraetProtokollRegelBool : RegisterAccess → Option GeraetePhase → Bool
  | .read _, none => true
  | .fallibleRead _ _, none => true
  | .write _ _, none => true
  | .write _ _, some .ready => true
  | .write _ _, some .reset => true
  | _, _ => false

/-- Every register step without a phase target satisfies the checker line. -/
theorem geraetProtokollRegel_register (access : RegisterAccess) :
    geraetProtokollRegelBool access none = true := by
  cases access with
  | read _ => rfl
  | fallibleRead _ _ => rfl
  | write _ _ => rfl

/-- The declared virtio row exposes the readable register at offset `0x70`. -/
theorem virtioRegisterLesbar :
    (Plattform.x86_64.virtio.register 0x70).any Register.read = true :=
  rfl

/-- The checker line is satisfiable for a declared device protocol: the virtio
    register `0x70` is readable and its read shape is accepted. -/
theorem geraetProtokollRegel_erfuellbar :
    ∃ offset, offset = 0x70 ∧ geraetProtokollRegelBool (.read offset) none = true ∧
      (Plattform.x86_64.virtio.register offset).any Register.read = true :=
  ⟨0x70, rfl, rfl, rfl⟩

end Gabbro.Core.Beobachtung
