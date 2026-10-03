/-
  Composition closing: thread-stack guard pages to fault delivery (lane 848).

  Producer/consumer interface closed here: the producers are the accepted
  fetched stack steps (`StackExecution.byteschritt_geholt_call/push` and
  the guard refusals `byteschritt_geholt_call_wache/push_wache`), the
  accepted step-level guard facts (`StackUnwind.wache_push/call_verweigert`),
  the accepted frame-save facts (`Stapel.sichereWort_rahmen`) and the
  accepted store facts (`Speicher.write64_rahmen`,
  `write64_verweigert_kein_effekt`); the consumer is fault delivery (a
  stack overflow into the guard loudly refuses as `byteschritt .verweigert`
  with no store outcome, so no neighbour byte can change). This file only
  composes already-accepted theorems; it re-proves no step, fetch, frame
  or store internals and defines no second interpreter or executor.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Speicher
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Byteschritt
import Grammatik.X86.Stapel
import Grammatik.X86.StackUnwind
import Grammatik.X86.StackExecution

namespace Gabbro.Grammatik.X86

/-- FETCHED CALL SUCCESS (composition leg): from actual call bytes, the
    composed byte step stores the correct next-RIP return word below the
    pre-state top and transfers control. Reuses the accepted
    `byteschritt_geholt_call` by name; generic over arbitrary admitted
    inputs. -/
theorem wachenCallWeiter (s : Zustand) (disp : BitVec 32)
    (suffix : List Byte) (m : Speicher)
    (hwin : StapelGeholt s (.call32 disp) suffix)
    (hexe : ausfuehrbarN s.speicher s.rip
      (encode (.call32 disp)).length = true)
    (hwr : write64 s.speicher (s.register Register.rsp - BitVec.ofNat 64 8)
      (ripNach s.rip (encode (.call32 disp)).length) = some m) :
    byteschritt s = .weiter (schrittCall s Register.rsp m
      (s.register Register.rsp - BitVec.ofNat 64 8)
      (ripNach s.rip (encode (.call32 disp)).length + dispWort disp)) :=
  byteschritt_geholt_call s disp suffix m hwin hexe hwr

/- CUTS:
    Proved here so far: fetched-call success through the composed byte
    step (`wachenCallWeiter`, reusing the accepted producer).
    NOT proved here, and not claimed:
    - Fetched-push success, call/push guard refusals with no-effect,
      return-into-guard refusal, frame-save neighbour preservation and
      the joint non-degenerate witness are still OPEN (next steps).
    - No source correspondence, no hardware correspondence, no TSO/GX
      bridge, no ABI/loader/entry/cost claim; `verweigert` is the absence
      of a transition, never a termination claim.
-/

#print axioms wachenCallWeiter

end Gabbro.Grammatik.X86
