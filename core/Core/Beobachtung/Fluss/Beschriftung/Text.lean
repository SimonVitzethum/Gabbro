module

public import Core.Beobachtung.Fluss.Beschriftung.Sprung

@[expose] public section

/-! Pinned duties for the text family. Each statement fixes the rule an instruction
    of that family gets, and says that the rule is sound for the public view. A
    prover supplies the `theorem`; the lead then adds the rule to `Befehl.FlussRegel`
    and replaces the fallback case for that instruction.

    Footprint summary: `textLiteral`, `textConcat` and `textLength` write one
    temporary from the read temporaries (`Schreibform`/`SchreibRegel`); `textIndex`
    and `substring` read public index temporaries and halt on an invalid offset, so
    the halt — which is always visible — coincides on both runs only when the
    inputs are public. -/

namespace Gabbro.Core.Ast.Semantik

open Maschine Beobachtung Katalog

/-- `textLiteral`: the constant text is written to `ziel`. -/
def TextLiteralSichtAussage : Prop :=
  ∀ (β : Beschriftung) (pc ziel : Nat) (decoded : List Char),
    β.SchreibRegel pc ziel [] →
    (Befehl.textLiteral ziel decoded).SichtErhaltendBei β pc

/-- `textConcat`: the texts in `basis` and `basis + 1` are concatenated,
    overwriting `basis`. -/
def TextConcatSichtAussage : Prop :=
  ∀ (β : Beschriftung) (pc basis a b : Nat),
    β.SchreibRegel pc basis [.temp basis, .temp (basis + 1)] →
    (Befehl.textConcat basis a b).SichtErhaltendBei β pc

/-- `textIndex`: the byte at the public offset in `basis + 1` is read from the
    public text in `basis`, overwriting `basis`; an invalid offset halts. -/
def TextIndexSichtAussage : Prop :=
  ∀ (β : Beschriftung) (pc basis capacity : Nat),
    oeffentlich (β.temp pc basis) = true →
    oeffentlich (β.temp pc (basis + 1)) = true →
    (∀ s, oeffentlich (β.temp (pc + 1) s) = true → oeffentlich (β.temp pc s) = true) →
    (∀ i, oeffentlich (β.lokal (pc + 1) i) = true → oeffentlich (β.lokal pc i) = true) →
    (Befehl.textIndex basis capacity).SichtErhaltendBei β pc

/-- `substring`: the slice between the public offsets in `basis + 1` and
    `basis + 2` is read from the public text in `basis`, overwriting `basis`;
    an invalid slice halts. -/
def SubstringSichtAussage : Prop :=
  ∀ (β : Beschriftung) (pc basis capacity : Nat),
    oeffentlich (β.temp pc basis) = true →
    oeffentlich (β.temp pc (basis + 1)) = true →
    oeffentlich (β.temp pc (basis + 2)) = true →
    (∀ s, oeffentlich (β.temp (pc + 1) s) = true → oeffentlich (β.temp pc s) = true) →
    (∀ i, oeffentlich (β.lokal (pc + 1) i) = true → oeffentlich (β.lokal pc i) = true) →
    (Befehl.substring basis capacity).SichtErhaltendBei β pc

/-- `textLength`: the length of the text in `basis` is written, overwriting
    `basis`. -/
def TextLengthSichtAussage : Prop :=
  ∀ (β : Beschriftung) (pc basis capacity : Nat),
    β.SchreibRegel pc basis [.temp basis] →
    (Befehl.textLength basis capacity).SichtErhaltendBei β pc

/-- The `textIndex` premises hold jointly. -/
theorem textIndexSicht_erfuellbar (basis capacity : Nat) :
    ∃ (β : Beschriftung) (pc : Nat), oeffentlich (β.temp pc basis) = true ∧
      oeffentlich (β.temp pc (basis + 1)) = true ∧
      (∀ s, oeffentlich (β.temp (pc + 1) s) = true →
        oeffentlich (β.temp pc s) = true) ∧
      (∀ i, oeffentlich (β.lokal (pc + 1) i) = true →
        oeffentlich (β.lokal pc i) = true) :=
  ⟨.alleOeffentlich, 0, alleOeffentlich_temp 0 basis,
    alleOeffentlich_temp 0 (basis + 1), fun s _ => alleOeffentlich_temp 0 s,
    fun i _ => alleOeffentlich_lokal 0 i⟩

/-- The `substring` premises hold jointly. -/
theorem substringSicht_erfuellbar (basis capacity : Nat) :
    ∃ (β : Beschriftung) (pc : Nat), oeffentlich (β.temp pc basis) = true ∧
      oeffentlich (β.temp pc (basis + 1)) = true ∧
      oeffentlich (β.temp pc (basis + 2)) = true ∧
      (∀ s, oeffentlich (β.temp (pc + 1) s) = true →
        oeffentlich (β.temp pc s) = true) ∧
      (∀ i, oeffentlich (β.lokal (pc + 1) i) = true →
        oeffentlich (β.lokal pc i) = true) :=
  ⟨.alleOeffentlich, 0, alleOeffentlich_temp 0 basis,
    alleOeffentlich_temp 0 (basis + 1), alleOeffentlich_temp 0 (basis + 2),
    fun s _ => alleOeffentlich_temp 0 s, fun i _ => alleOeffentlich_lokal 0 i⟩

end Gabbro.Core.Ast.Semantik
