module

public import Core.Beobachtung.Fluss.Beschriftung.Sprung

@[expose] public section

/-! Pinned duties for the variant family. Each statement fixes the rule an
    instruction of that family gets, and says that the rule is sound for the public
    view. A prover supplies the `theorem`; the lead then adds the rule to
    `Befehl.FlussRegel` and replaces the fallback case for that instruction.

    Footprint summary: `baueVariante` writes one temporary from the payload
    temporary in the same slot (`Schreibform`/`SchreibRegel`); `optionIstBesetzt`
    likewise; `definiereVariante`, `definiereTraeger` and `definiereEffektgruppe`
    push one static schema entry onto the locals and the always-public global
    table; `waehleUmgebung` pushes one static entry onto the always-visible
    environment; `waehleVariante` branches on the public tag in `source` to one of
    the static branch targets, optionally pushing the payload. -/

namespace Gabbro.Core.Ast.Semantik

open Maschine Beobachtung Katalog

/-- `definiereVariante`: one static schema entry is pushed onto the locals and the
    always-public global table. -/
def DefiniereVarianteSichtAussage : Prop :=
  ∀ (β : Beschriftung) (pc : Nat) (name : List Char) (labels : List Identifier)
    (cases : List (Option (Ty .value))),
    (∀ s, oeffentlich (β.temp (pc + 1) s) = true → oeffentlich (β.temp pc s) = true) →
    (∀ i, oeffentlich (β.lokal (pc + 1) (i + 1)) = true →
      oeffentlich (β.lokal pc i) = true) →
    (Befehl.definiereVariante name labels cases).SichtErhaltendBei β pc

/-- `baueVariante`: the payload temporary `ziel` is injected into the variant,
    overwriting `ziel`. -/
def BaueVarianteSichtAussage : Prop :=
  ∀ (β : Beschriftung) (pc ziel : Nat) (name : List Char) (labels : List Identifier)
    (cases : List (Option (Ty .value))) (index : Fin cases.length),
    β.SchreibRegel pc ziel [.temp ziel] →
    (Befehl.baueVariante ziel name labels cases index).SichtErhaltendBei β pc

/-- `waehleVariante`: the tag in `source` must be public (the branch is public
    control); every static branch target keeps the labels at least as secret, and a
    binding branch takes the payload from the public source. -/
def WaehleVarianteSichtAussage : Prop :=
  ∀ (β : Beschriftung) (pc source : Nat) (name : List Char) (labels : List Identifier)
    (cases : List (Option (Ty .value))) (branches : List (Nat × Bool)),
    oeffentlich (β.temp pc source) = true →
    (∀ b ∈ branches,
      (∀ s, oeffentlich (β.temp (pc + b.1) s) = true →
        oeffentlich (β.temp pc s) = true) ∧
      (∀ i, oeffentlich (β.lokal (pc + b.1) (i + (if b.2 then 1 else 0))) = true →
        oeffentlich (β.lokal pc i) = true) ∧
      (b.2 = true → oeffentlich (β.lokal (pc + b.1) 0) = true →
        oeffentlich (β.temp pc source) = true)) →
    (Befehl.waehleVariante source name labels cases branches).SichtErhaltendBei β pc

/-- `definiereTraeger`: one static schema entry is pushed onto the locals and the
    always-public global table. -/
def DefiniereTraegerSichtAussage : Prop :=
  ∀ (β : Beschriftung) (pc count : Nat) (labels : List (List Char)) (layout : Ty .value)
    (exported : Bool),
    (∀ s, oeffentlich (β.temp (pc + 1) s) = true → oeffentlich (β.temp pc s) = true) →
    (∀ i, oeffentlich (β.lokal (pc + 1) (i + 1)) = true →
      oeffentlich (β.lokal pc i) = true) →
    (Befehl.definiereTraeger count labels layout exported).SichtErhaltendBei β pc

/-- `optionIstBesetzt`: the presence bit is computed from `ziel`, overwriting
    `ziel`. -/
def OptionIstBesetztSichtAussage : Prop :=
  ∀ (β : Beschriftung) (pc ziel count : Nat),
    β.SchreibRegel pc ziel [.temp ziel] →
    (Befehl.optionIstBesetzt ziel count).SichtErhaltendBei β pc

/-- `definiereEffektgruppe`: one static schema entry is pushed onto the locals and
    the always-public global table. -/
def DefiniereEffektgruppeSichtAussage : Prop :=
  ∀ (β : Beschriftung) (pc : Nat) (effects : List CarrierEffect),
    (∀ s, oeffentlich (β.temp (pc + 1) s) = true → oeffentlich (β.temp pc s) = true) →
    (∀ i, oeffentlich (β.lokal (pc + 1) (i + 1)) = true →
      oeffentlich (β.lokal pc i) = true) →
    (Befehl.definiereEffektgruppe effects).SichtErhaltendBei β pc

/-- `waehleUmgebung`: one static entry is pushed onto the always-visible
    environment; temporaries and locals fall through. -/
def WaehleUmgebungSichtAussage : Prop :=
  ∀ (β : Beschriftung) (pc : Nat) (name : Identifier) (abi : Katalog.DienstAbi)
    (row : Katalog.FirmwareZeile),
    (∀ s, oeffentlich (β.temp (pc + 1) s) = true → oeffentlich (β.temp pc s) = true) →
    (∀ i, oeffentlich (β.lokal (pc + 1) i) = true → oeffentlich (β.lokal pc i) = true) →
    (Befehl.waehleUmgebung name abi row).SichtErhaltendBei β pc

/-- The `waehleVariante` premises hold jointly. -/
theorem waehleVarianteSicht_erfuellbar (source : Nat) (name : List Char)
    (labels : List Identifier) (cases : List (Option (Ty .value)))
    (branches : List (Nat × Bool)) :
    ∃ β pc, oeffentlich (β.temp pc source) = true ∧
      (∀ b ∈ branches,
        (∀ s, oeffentlich (β.temp (pc + b.1) s) = true →
          oeffentlich (β.temp pc s) = true) ∧
        (∀ i, oeffentlich (β.lokal (pc + b.1) (i + (if b.2 then 1 else 0))) = true →
          oeffentlich (β.lokal pc i) = true) ∧
        (b.2 = true → oeffentlich (β.lokal (pc + b.1) 0) = true →
          oeffentlich (β.temp pc source) = true)) :=
  ⟨.alleOeffentlich, 0, alleOeffentlich_temp 0 source,
    fun b _ => ⟨fun s _ => alleOeffentlich_temp 0 s,
      fun i _ => alleOeffentlich_lokal 0 i,
      fun _ _ => alleOeffentlich_temp 0 source⟩⟩

end Gabbro.Core.Ast.Semantik
