module

public import Core.Beobachtung.Fluss.Beweise.Geraet
public import Core.Ast.LowLevel.DeviceUnit

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine
open Gabbro.Core.Ast.LowLevel.Device

/-- A device consume step is silent: the plan is internal with a `verbrauche`
    action, so no memory label, no outside event, no commit, no output, no
    time mark and no new end is recorded. -/
theorem geraete_consume_still {k : Katalog} {binding : Binding k} {access : RegisterAccess}
    {required : GeraetePhase} {target : Option GeraetePhase} {c : Kontext}
    {s u : State} {plan : Plan} {answer : AntwortEreignis}
    (owned : Befugt binding required access s c)
    (pending : (s.lokal c).pending = some (binding.question access))
    (ready : s.naechsteAntwort c = some answer)
    (same : answer.question = binding.question access)
    {t : Nat} {ρ : Lauf (Gabbro.Core.Ast.LowLevel.Device.unit k binding
      (Rule.machine binding access required target))} {predictor : Praediktor}
    {spur : SchrittSpur Nat UInt8} {s' : State}
    (aus : FuehrtSchrittAus (Gabbro.Core.Ast.LowLevel.Device.unit k binding
      (Rule.machine binding access required target)).einrichtung t c s
      (setFrame s c { s.lokal c with
        pending := none
        last := some (access.result answer.reply)
        phases := match access.result answer.reply, target with
          | .written, some phase => Function.update (s.lokal c).phases binding.object (some phase)
          | _, _ => (s.lokal c).phases })
      { internal with aktion := .verbrauche answer } plan spur s') :
    spur.aussen = [] := by
  obtain ⟨_, _, _, _, aktion, _, _⟩ := aus
  cases aktion
  rfl

end Gabbro.Core.Beobachtung
