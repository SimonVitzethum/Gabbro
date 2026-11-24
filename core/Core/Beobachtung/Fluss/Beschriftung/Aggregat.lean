module

public import Core.Beobachtung.Fluss.Beschriftung.Sprung

@[expose] public section

/-! Pinned duties for the aggregate family. Each statement fixes the rule an
    instruction of that family gets, and says that the rule is sound for the public
    view. A prover supplies the `theorem`; the lead then adds the rule to
    `Befehl.FlussRegel` and replaces the fallback case for that instruction.

    Footprint summary: `baueArray`, `baueTupel` and `baueRecord` write one temporary
    from several read temporaries (the `Schreibform`/`SchreibRegel` pattern);
    `liesArray`, `liesTupelfeld` and `liesRecordFeld` read and overwrite the same
    temporary (index or payload plus base); `bindeTupel` pushes the kept components
    onto the locals; `definiereRecord` pushes one static schema entry onto the
    locals and the always-public global table; `setzeRecordFeld` overwrites one
    local from a read temporary and the old local record. -/

namespace Gabbro.Core.Ast.Semantik

open Maschine Beobachtung Katalog

/-- The consecutive temporary window an aggregate builder reads. -/
def tempBereich (dst count : Nat) : List Komp :=
  (List.range count).map fun i => Komp.temp (dst + i)

/-- The number of locals `bindeTupel` pushes: one per kept component. -/
def behalteneTupel (types : List (Ty .value)) (bind : List Bool) : Nat :=
  ((types.zip bind).filter fun (_, keep) => keep).length

/-- `baueArray`: the array in `ziel` is built from the `count` temporaries at
    `ziel` to `ziel + count - 1`. -/
def BaueArraySichtAussage : Prop :=
  ∀ (β : Beschriftung) (pc ziel : Nat) (element : Ty .value) (count : Nat),
    β.SchreibRegel pc ziel (tempBereich ziel count) →
    (Befehl.baueArray ziel element count).SichtErhaltendBei β pc

/-- `liesArray`: the element is read from the array in `basis` at the index in
    `basis + 1`, overwriting `basis`. -/
def LiesArraySichtAussage : Prop :=
  ∀ (β : Beschriftung) (pc basis : Nat) (element : Ty .value) (count : Nat),
    β.SchreibRegel pc basis [.temp basis, .temp (basis + 1)] →
    (Befehl.liesArray basis element count).SichtErhaltendBei β pc

/-- `baueTupel`: the tuple in `ziel` is built from the temporaries at `ziel`
    upwards. -/
def BaueTupelSichtAussage : Prop :=
  ∀ (β : Beschriftung) (pc ziel : Nat) (types : List (Ty .value)),
    β.SchreibRegel pc ziel (tempBereich ziel types.length) →
    (Befehl.baueTupel ziel types).SichtErhaltendBei β pc

/-- `liesTupelfeld`: the field is read from the tuple in `basis`, overwriting
    `basis`. -/
def LiesTupelfeldSichtAussage : Prop :=
  ∀ (β : Beschriftung) (pc basis : Nat) (types : List (Ty .value))
    (index : Fin types.length),
    β.SchreibRegel pc basis [.temp basis] →
    (Befehl.liesTupelfeld basis types index).SichtErhaltendBei β pc

/-- `bindeTupel`: the kept components of the tuple in `quelle` are pushed onto the
    locals. The pushed count is statically known; on a conversion failure nothing
    is pushed, hence both the identity and the shifted tail rule. -/
def BindeTupelSichtAussage : Prop :=
  ∀ (β : Beschriftung) (pc quelle : Nat) (types : List (Ty .value)) (bind : List Bool),
    oeffentlich (β.temp pc quelle) = true →
    (∀ i, oeffentlich (β.lokal (pc + 1) i) = true →
      oeffentlich (β.lokal pc i) = true) →
    (∀ i, oeffentlich (β.lokal (pc + 1) (i + behalteneTupel types bind)) = true →
      oeffentlich (β.lokal pc i) = true) →
    (Befehl.bindeTupel quelle types bind).SichtErhaltendBei β pc

/-- `definiereRecord`: one static schema entry is pushed onto the locals and the
    always-public global table. -/
def DefiniereRecordSichtAussage : Prop :=
  ∀ (β : Beschriftung) (pc : Nat) (name : List Char) (labels : List Identifier)
    (types : List (Ty .value)),
    (∀ s, oeffentlich (β.temp (pc + 1) s) = true → oeffentlich (β.temp pc s) = true) →
    (∀ i, oeffentlich (β.lokal (pc + 1) (i + 1)) = true →
      oeffentlich (β.lokal pc i) = true) →
    (Befehl.definiereRecord name labels types).SichtErhaltendBei β pc

/-- `baueRecord`: the record in `ziel` is built from the source temporaries. -/
def BaueRecordSichtAussage : Prop :=
  ∀ (β : Beschriftung) (pc ziel : Nat) (name : List Char) (labels : List Identifier)
    (types : List (Ty .value)) (sources : List Nat),
    β.SchreibRegel pc ziel (sources.map Komp.temp) →
    (Befehl.baueRecord ziel name labels types sources).SichtErhaltendBei β pc

/-- `liesRecordFeld`: the field is read from the record in `basis`, overwriting
    `basis`. -/
def LiesRecordFeldSichtAussage : Prop :=
  ∀ (β : Beschriftung) (pc basis : Nat) (name : List Char) (labels : List Identifier)
    (types : List (Ty .value)) (index : Fin types.length),
    β.SchreibRegel pc basis [.temp basis] →
    (Befehl.liesRecordFeld basis name labels types index).SichtErhaltendBei β pc

/-- `setzeRecordFeld`: local `indexLocal` is overwritten by the old record with the
    field from `source`. -/
def SetzeRecordFeldSichtAussage : Prop :=
  ∀ (β : Beschriftung) (pc source indexLocal : Nat) (name : List Char)
    (labels : List Identifier) (types : List (Ty .value)) (index : Fin types.length),
    (∀ s, oeffentlich (β.temp (pc + 1) s) = true → oeffentlich (β.temp pc s) = true) →
    (∀ j, j ≠ indexLocal → oeffentlich (β.lokal (pc + 1) j) = true →
      oeffentlich (β.lokal pc j) = true) →
    (oeffentlich (β.lokal (pc + 1) indexLocal) = true →
      oeffentlich (β.temp pc source) = true) →
    (oeffentlich (β.lokal (pc + 1) indexLocal) = true →
      oeffentlich (β.lokal pc indexLocal) = true) →
    (Befehl.setzeRecordFeld source indexLocal name labels types
      index).SichtErhaltendBei β pc

/-- The `baueArray` premises hold jointly (shared `SchreibRegel` bundle). -/
theorem baueArraySicht_erfuellbar (ziel : Nat) (element : Ty .value) (count : Nat) :
    ∃ (β : Beschriftung) (pc : Nat), β.SchreibRegel pc ziel (tempBereich ziel count) :=
  ⟨.alleOeffentlich, 0, schreibRegel_alleOeffentlich 0 ziel _⟩

/-- The `baueTupel` premises hold jointly (shared `SchreibRegel` bundle). -/
theorem baueTupelSicht_erfuellbar (ziel : Nat) (types : List (Ty .value)) :
    ∃ (β : Beschriftung) (pc : Nat), β.SchreibRegel pc ziel (tempBereich ziel types.length) :=
  ⟨.alleOeffentlich, 0, schreibRegel_alleOeffentlich 0 ziel _⟩

/-- The `bindeTupel` premises hold jointly. -/
theorem bindeTupelSicht_erfuellbar (quelle : Nat) (types : List (Ty .value))
    (bind : List Bool) :
    ∃ (β : Beschriftung) (pc : Nat), oeffentlich (β.temp pc quelle) = true ∧
      (∀ i, oeffentlich (β.lokal (pc + 1) i) = true →
        oeffentlich (β.lokal pc i) = true) ∧
      (∀ i, oeffentlich (β.lokal (pc + 1) (i + behalteneTupel types bind)) = true →
        oeffentlich (β.lokal pc i) = true) :=
  ⟨.alleOeffentlich, 0, alleOeffentlich_temp 0 quelle,
    fun i _ => alleOeffentlich_lokal 0 i, fun i _ => alleOeffentlich_lokal 0 i⟩

/-- The `baueRecord` premises hold jointly (shared `SchreibRegel` bundle). -/
theorem baueRecordSicht_erfuellbar (ziel : Nat) (name : List Char)
    (labels : List Identifier) (types : List (Ty .value)) (sources : List Nat) :
    ∃ (β : Beschriftung) (pc : Nat), β.SchreibRegel pc ziel (sources.map Komp.temp) :=
  ⟨.alleOeffentlich, 0, schreibRegel_alleOeffentlich 0 ziel _⟩

/-- The `setzeRecordFeld` premises hold jointly. -/
theorem setzeRecordFeldSicht_erfuellbar (source indexLocal : Nat) (name : List Char)
    (labels : List Identifier) (types : List (Ty .value)) (index : Fin types.length) :
    ∃ (β : Beschriftung) (pc : Nat), (∀ s, oeffentlich (β.temp (pc + 1) s) = true →
        oeffentlich (β.temp pc s) = true) ∧
      (∀ j, j ≠ indexLocal → oeffentlich (β.lokal (pc + 1) j) = true →
        oeffentlich (β.lokal pc j) = true) ∧
      (oeffentlich (β.lokal (pc + 1) indexLocal) = true →
        oeffentlich (β.temp pc source) = true) ∧
      (oeffentlich (β.lokal (pc + 1) indexLocal) = true →
        oeffentlich (β.lokal pc indexLocal) = true) :=
  ⟨.alleOeffentlich, 0, fun s _ => alleOeffentlich_temp 0 s,
    fun j _ _ => alleOeffentlich_lokal 0 j, fun _ => alleOeffentlich_temp 0 source,
    fun _ => alleOeffentlich_lokal 0 indexLocal⟩

end Gabbro.Core.Ast.Semantik
