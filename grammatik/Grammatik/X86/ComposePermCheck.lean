/-
  Composition closing: per-access permission check to fetch/decode/execute
  (lane 857).

  Producer/consumer interface closed here: the producers are the accepted
  permission primitives (`Speicher.read64`/`write64` with their `lesbar8` /
  `schreibbar8` checks, `Byteschritt` fetch with its `ausfuehrbarN` check)
  together with the accepted step/footprint theorems (`Zugriffe`,
  `AccessExecution`, `WordAtomicity`); the consumer is the checked closing
  step below, which runs only the existing `byteschritt`. Nothing is
  redefined here: no second loader, decoder, executor or ISA model.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Speicher
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Byteschritt
import Grammatik.X86.Zugriffe
import Grammatik.X86.AccessExecution
import Grammatik.X86.WordAtomicity

namespace Gabbro.Grammatik.X86

/-- Checked permission bundle for one fetched instruction: the consumed
    fetch prefix is executable, and every footprint address the accepted
    extraction names carries its data permission. Stated per byte address,
    so an unchecked access is unrepresentable, not merely absent. -/
def PermGeprueft (s : Zustand) (d : Decodiert) : Prop :=
  ausfuehrbarN s.speicher s.rip d.laenge = true ∧
  (∀ x, x ∈ (zugriff d s).lesen → s.speicher.lesbar x = true) ∧
  (∀ x, x ∈ (zugriff d s).schreiben → s.speicher.schreibbar x = true)

/- CUTS:
    Proved here so far: the checked bundle `PermGeprueft` (fetch prefix
    plus per-byte footprint permissions).
    NOT proved here, and not claimed: success direction (realised step
    implies the bundle), refusal direction (permission failure refuses),
    the closing theorem `ComposePermCheck_verbindung` and its joint
    witness `ComposePermCheck_verbindung_zeuge`.
-/

#print axioms PermGeprueft

end Gabbro.Grammatik.X86
