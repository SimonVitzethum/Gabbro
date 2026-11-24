module

public import Core.Beobachtung.Fluss.Beschriftung.Sprung

@[expose] public section

/-! Pinned duties for the next label rules. Each statement fixes the rule an instruction of the
    control-flow family gets, and says that the rule is sound for the public view. A prover
    supplies the `theorem`; the lead then adds the rule to `Befehl.FlussRegel` and replaces the
    fallback case for that instruction. The statements are proved in `AufgabenBeweise`. -/

namespace Gabbro.Core.Ast.Semantik

open Maschine Beobachtung

/-- `zuweisen`: the local `index` is overwritten from the temporary `quelle`. -/
def ZuweisenSichtAussage : Prop :=
  ∀ (β : Beschriftung) (pc quelle index : Nat) (zieltyp : Ty .value),
    (∀ s, oeffentlich (β.temp (pc + 1) s) = true → oeffentlich (β.temp pc s) = true) →
    (∀ i, i ≠ index → oeffentlich (β.lokal (pc + 1) i) = true →
      oeffentlich (β.lokal pc i) = true) →
    (oeffentlich (β.lokal (pc + 1) index) = true → oeffentlich (β.temp pc quelle) = true) →
    (Befehl.zuweisen quelle index zieltyp).SichtErhaltendBei β pc

/-- `binden`: the temporary `quelle` is pushed as the new local 0; the others move up by one. -/
def BindenSichtAussage : Prop :=
  ∀ (β : Beschriftung) (pc : Nat) (name : Identifier) (quelle : Nat),
    (∀ s, oeffentlich (β.temp (pc + 1) s) = true → oeffentlich (β.temp pc s) = true) →
    (∀ i, oeffentlich (β.lokal (pc + 1) (i + 1)) = true → oeffentlich (β.lokal pc i) = true) →
    (oeffentlich (β.lokal (pc + 1) 0) = true → oeffentlich (β.temp pc quelle) = true) →
    (Befehl.binden name quelle).SichtErhaltendBei β pc

/-- `bindeWert`: as `binden`, with a conversion; a global binding copies the value into the
    always-public function table, so its source must be public. -/
def BindeWertSichtAussage : Prop :=
  ∀ (β : Beschriftung) (pc quelle : Nat) (ziel : Ty .value) (global : Bool),
    (∀ s, oeffentlich (β.temp (pc + 1) s) = true → oeffentlich (β.temp pc s) = true) →
    (∀ i, oeffentlich (β.lokal (pc + 1) (i + 1)) = true → oeffentlich (β.lokal pc i) = true) →
    (oeffentlich (β.lokal (pc + 1) 0) = true → oeffentlich (β.temp pc quelle) = true) →
    (global = true → oeffentlich (β.temp pc quelle) = true) →
    (Befehl.bindeWert quelle ziel global).SichtErhaltendBei β pc

/-- `blockEnde`: the `count` innermost locals are dropped. -/
def BlockEndeSichtAussage : Prop :=
  ∀ (β : Beschriftung) (pc count : Nat),
    (∀ s, oeffentlich (β.temp (pc + 1) s) = true → oeffentlich (β.temp pc s) = true) →
    (∀ i, oeffentlich (β.lokal (pc + 1) i) = true → oeffentlich (β.lokal pc (i + count)) = true) →
    (Befehl.blockEnde count).SichtErhaltendBei β pc

end Gabbro.Core.Ast.Semantik
