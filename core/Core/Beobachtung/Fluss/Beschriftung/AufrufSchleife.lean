module

public import Core.Beobachtung.Fluss.Beschriftung.Sprung

@[expose] public section

/-! Pinned duties for the call and loop family. Each statement fixes the rule an
    instruction of that family gets, and says that the rule is sound for the public
    view. A prover supplies the `theorem`; the lead then adds the rule to
    `Befehl.FlussRegel` and replaces the fallback case for that instruction.

    Footprint summary: `definiere` and `zurueckSprung` only move the program counter
    (`definiere` also pushes one static entry onto the always-public function table);
    `rufe` clears the temporaries, rebuilds the locals from public temporaries and
    the visible globals, and pushes the whole frame onto the visible continuation
    stack, so every temporary and local at `pc` must be public; `rueckVoid` pops the
    visible continuation stack (the value-returning sibling lives with the
    control-flow duties); `pruefeMass` and `setzePasszahl` read one tested temporary and
    write the always-visible measure and counter tables; `whileTest`, `forTest` and
    `forNaechster` branch on a public test (a temporary, respectively local 0);
    `forAnfang` reads two public bound temporaries and either jumps or pushes one
    freshly converted local. A secret test would fork the visible control flow, so
    every test is required public. -/

namespace Gabbro.Core.Ast.Semantik

open Maschine Beobachtung Katalog

/-- `definiere`: the function table grows by one static entry, control jumps to
    `pc + ueberspringe`. -/
def DefiniereSichtAussage : Prop :=
  ∀ (β : Beschriftung) (pc : Nat) (name : Identifier) (parameter : List (Ty .value))
    (result : Option (Ty .value)) (globale ueberspringe : Nat) (misstAbstieg : Bool)
    (ruft : List Rufstelle) (effects : Option (List CarrierEffect)),
    (∀ s, oeffentlich (β.temp (pc + ueberspringe) s) = true →
      oeffentlich (β.temp pc s) = true) →
    (∀ i, oeffentlich (β.lokal (pc + ueberspringe) i) = true →
      oeffentlich (β.lokal pc i) = true) →
    (Befehl.definiere name parameter result globale ueberspringe misstAbstieg ruft
      effects).SichtErhaltendBei β pc

/-- `rufe`: the call clears the temporaries and rebuilds the locals from the call
    arguments and the visible globals, pushing the whole frame onto the visible
    continuation stack. Since the saved frame stays visible, every temporary and
    every local at `pc` must be public. No successor labels are needed: cleared
    temporaries are equal under every label, and rebuilt locals are equal values. -/
def RufeSichtAussage : Prop :=
  ∀ (β : Beschriftung) (pc : Nat) (name : Identifier) (args : List (Ty .value))
    (bind : Option (Ty .value)),
    (∀ s, oeffentlich (β.temp pc s) = true) →
    (∀ i, oeffentlich (β.lokal pc i) = true) →
    (Befehl.rufe name args bind).SichtErhaltendBei β pc

/-- `rueckVoid`: the visible continuation stack is popped; with an empty stack the
    frame ends. The successor is `pc + 1` only in the empty-stack case, hence the
    fall-through labels. -/
def RueckVoidSichtAussage : Prop :=
  ∀ (β : Beschriftung) (pc : Nat),
    (∀ s, oeffentlich (β.temp (pc + 1) s) = true → oeffentlich (β.temp pc s) = true) →
    (∀ i, oeffentlich (β.lokal (pc + 1) i) = true → oeffentlich (β.lokal pc i) = true) →
    Befehl.rueckVoid.SichtErhaltendBei β pc

/-- `pruefeMass`: the tested temporary must be public, since both the halt reasons
    and the always-visible measure are derived from it. -/
def PruefeMassSichtAussage : Prop :=
  ∀ (β : Beschriftung) (pc quelle : Nat),
    oeffentlich (β.temp pc quelle) = true →
    (∀ s, oeffentlich (β.temp (pc + 1) s) = true → oeffentlich (β.temp pc s) = true) →
    (∀ i, oeffentlich (β.lokal (pc + 1) i) = true → oeffentlich (β.lokal pc i) = true) →
    (Befehl.pruefeMass quelle).SichtErhaltendBei β pc

/-- `setzePasszahl`: the tested temporary must be public, since both the halt reason
    and the always-visible counter entry are derived from it. -/
def SetzePasszahlSichtAussage : Prop :=
  ∀ (β : Beschriftung) (pc quelle stelle : Nat),
    oeffentlich (β.temp pc quelle) = true →
    (∀ s, oeffentlich (β.temp (pc + 1) s) = true → oeffentlich (β.temp pc s) = true) →
    (∀ i, oeffentlich (β.lokal (pc + 1) i) = true → oeffentlich (β.lokal pc i) = true) →
    (Befehl.setzePasszahl quelle stelle).SichtErhaltendBei β pc

/-- `whileTest`: the tested temporary must be public (the branch is public control),
    and both successors keep the labels at least as secret. -/
def WhileTestSichtAussage : Prop :=
  ∀ (β : Beschriftung) (pc quelle ende : Nat) (handler : Identifier),
    oeffentlich (β.temp pc quelle) = true →
    (∀ q, q = pc + 1 ∨ q = pc + ende →
      (∀ s, oeffentlich (β.temp q s) = true → oeffentlich (β.temp pc s) = true) ∧
      (∀ i, oeffentlich (β.lokal q i) = true → oeffentlich (β.lokal pc i) = true)) →
    (Befehl.whileTest quelle ende handler).SichtErhaltendBei β pc

/-- `forAnfang`: both bound temporaries must be public (they decide between jumping
    and pushing, and the pushed initial value and the always-visible bound and
    counter entries are derived from them). -/
def ForAnfangSichtAussage : Prop :=
  ∀ (β : Beschriftung) (pc unter ober : Nat) (index : Ty .value) (skipEmpty : Nat)
    (shadowed missingHandler : Bool),
    oeffentlich (β.temp pc unter) = true →
    oeffentlich (β.temp pc ober) = true →
    (∀ s, oeffentlich (β.temp (pc + 1) s) = true → oeffentlich (β.temp pc s) = true) →
    (∀ i, oeffentlich (β.lokal (pc + 1) (i + 1)) = true →
      oeffentlich (β.lokal pc i) = true) →
    (oeffentlich (β.lokal (pc + 1) 0) = true → oeffentlich (β.temp pc unter) = true) →
    (∀ s, oeffentlich (β.temp (pc + skipEmpty) s) = true →
      oeffentlich (β.temp pc s) = true) →
    (∀ i, oeffentlich (β.lokal (pc + skipEmpty) i) = true →
      oeffentlich (β.lokal pc i) = true) →
    (Befehl.forAnfang unter ober index skipEmpty shadowed
      missingHandler).SichtErhaltendBei β pc

/-- `forTest`: local 0 holds the loop counter and decides the public branch, so it
    must be public; both successors keep the labels at least as secret. -/
def ForTestSichtAussage : Prop :=
  ∀ (β : Beschriftung) (pc ende : Nat) (handler : Option Identifier),
    oeffentlich (β.lokal pc 0) = true →
    (∀ q, q = pc + 1 ∨ q = pc + ende →
      (∀ s, oeffentlich (β.temp q s) = true → oeffentlich (β.temp pc s) = true) ∧
      (∀ i, oeffentlich (β.lokal q i) = true → oeffentlich (β.lokal pc i) = true)) →
    (Befehl.forTest ende handler).SichtErhaltendBei β pc

/-- `forNaechster`: local 0 holds the loop counter; the incremented head overwrites
    it and control jumps back by `zurueck`. -/
def ForNaechsterSichtAussage : Prop :=
  ∀ (β : Beschriftung) (pc zurueck : Nat) (index : Ty .value),
    oeffentlich (β.lokal pc 0) = true →
    (∀ s, oeffentlich (β.temp (pc - zurueck) s) = true →
      oeffentlich (β.temp pc s) = true) →
    (∀ i, i ≠ 0 → oeffentlich (β.lokal (pc - zurueck) i) = true →
      oeffentlich (β.lokal pc i) = true) →
    (oeffentlich (β.lokal (pc - zurueck) 0) = true →
      oeffentlich (β.lokal pc 0) = true) →
    (Befehl.forNaechster zurueck index).SichtErhaltendBei β pc

/-- `zurueckSprung`: only the program counter moves, backwards by `abstand`. -/
def ZurueckSprungSichtAussage : Prop :=
  ∀ (β : Beschriftung) (pc abstand : Nat),
    (∀ s, oeffentlich (β.temp (pc - abstand) s) = true →
      oeffentlich (β.temp pc s) = true) →
    (∀ i, oeffentlich (β.lokal (pc - abstand) i) = true →
      oeffentlich (β.lokal pc i) = true) →
    (Befehl.zurueckSprung abstand).SichtErhaltendBei β pc

/-- The `rufe` premises hold jointly: under the all-public declaration everything
    is public. -/
theorem rufeSicht_erfuellbar (name : Identifier) (args : List (Ty .value))
    (bind : Option (Ty .value)) :
    ∃ (β : Beschriftung) (pc : Nat), (∀ s, oeffentlich (β.temp pc s) = true) ∧
      (∀ i, oeffentlich (β.lokal pc i) = true) :=
  ⟨.alleOeffentlich, 0, fun s => alleOeffentlich_temp 0 s,
    fun i => alleOeffentlich_lokal 0 i⟩

/-- The `rueckVoid` premises hold jointly. -/
theorem rueckVoidSicht_erfuellbar :
    ∃ (β : Beschriftung) (pc : Nat), (∀ s, oeffentlich (β.temp (pc + 1) s) = true →
        oeffentlich (β.temp pc s) = true) ∧
      (∀ i, oeffentlich (β.lokal (pc + 1) i) = true →
        oeffentlich (β.lokal pc i) = true) :=
  ⟨.alleOeffentlich, 0, fun s _ => alleOeffentlich_temp 0 s,
    fun i _ => alleOeffentlich_lokal 0 i⟩

/-- The `pruefeMass` premises hold jointly. -/
theorem pruefeMassSicht_erfuellbar (quelle : Nat) :
    ∃ (β : Beschriftung) (pc : Nat), oeffentlich (β.temp pc quelle) = true ∧
      (∀ s, oeffentlich (β.temp (pc + 1) s) = true →
        oeffentlich (β.temp pc s) = true) ∧
      (∀ i, oeffentlich (β.lokal (pc + 1) i) = true →
        oeffentlich (β.lokal pc i) = true) :=
  ⟨.alleOeffentlich, 0, alleOeffentlich_temp 0 quelle,
    fun s _ => alleOeffentlich_temp 0 s, fun i _ => alleOeffentlich_lokal 0 i⟩

/-- The `whileTest` premises hold jointly. -/
theorem whileTestSicht_erfuellbar (quelle ende : Nat) (handler : Identifier) :
    ∃ (β : Beschriftung) (pc : Nat), oeffentlich (β.temp pc quelle) = true ∧
      (∀ q, q = pc + 1 ∨ q = pc + ende →
        (∀ s, oeffentlich (β.temp q s) = true → oeffentlich (β.temp pc s) = true) ∧
        (∀ i, oeffentlich (β.lokal q i) = true → oeffentlich (β.lokal pc i) = true)) :=
  ⟨.alleOeffentlich, 0, alleOeffentlich_temp 0 quelle,
    fun q _ => ⟨fun s _ => alleOeffentlich_temp 0 s,
      fun i _ => alleOeffentlich_lokal 0 i⟩⟩

/-- The `forAnfang` premises hold jointly. -/
theorem forAnfangSicht_erfuellbar (unter ober : Nat) (index : Ty .value)
    (skipEmpty : Nat) (shadowed missingHandler : Bool) :
    ∃ (β : Beschriftung) (pc : Nat), oeffentlich (β.temp pc unter) = true ∧
      oeffentlich (β.temp pc ober) = true ∧
      (∀ s, oeffentlich (β.temp (pc + 1) s) = true →
        oeffentlich (β.temp pc s) = true) ∧
      (∀ i, oeffentlich (β.lokal (pc + 1) (i + 1)) = true →
        oeffentlich (β.lokal pc i) = true) ∧
      (oeffentlich (β.lokal (pc + 1) 0) = true →
        oeffentlich (β.temp pc unter) = true) ∧
      (∀ s, oeffentlich (β.temp (pc + skipEmpty) s) = true →
        oeffentlich (β.temp pc s) = true) ∧
      (∀ i, oeffentlich (β.lokal (pc + skipEmpty) i) = true →
        oeffentlich (β.lokal pc i) = true) :=
  ⟨.alleOeffentlich, 0, alleOeffentlich_temp 0 unter, alleOeffentlich_temp 0 ober,
    fun s _ => alleOeffentlich_temp 0 s, fun i _ => alleOeffentlich_lokal 0 i,
    fun _ => alleOeffentlich_temp 0 unter, fun s _ => alleOeffentlich_temp 0 s,
    fun i _ => alleOeffentlich_lokal 0 i⟩

/-- The `forTest` premises hold jointly. -/
theorem forTestSicht_erfuellbar (ende : Nat) (handler : Option Identifier) :
    ∃ (β : Beschriftung) (pc : Nat), oeffentlich (β.lokal pc 0) = true ∧
      (∀ q, q = pc + 1 ∨ q = pc + ende →
        (∀ s, oeffentlich (β.temp q s) = true → oeffentlich (β.temp pc s) = true) ∧
        (∀ i, oeffentlich (β.lokal q i) = true → oeffentlich (β.lokal pc i) = true)) :=
  ⟨.alleOeffentlich, 0, alleOeffentlich_lokal 0 0,
    fun q _ => ⟨fun s _ => alleOeffentlich_temp 0 s,
      fun i _ => alleOeffentlich_lokal 0 i⟩⟩

/-- The `forNaechster` premises hold jointly. -/
theorem forNaechsterSicht_erfuellbar (zurueck : Nat) (index : Ty .value) :
    ∃ (β : Beschriftung) (pc : Nat), oeffentlich (β.lokal pc 0) = true ∧
      (∀ s, oeffentlich (β.temp (pc - zurueck) s) = true →
        oeffentlich (β.temp pc s) = true) ∧
      (∀ i, i ≠ 0 → oeffentlich (β.lokal (pc - zurueck) i) = true →
        oeffentlich (β.lokal pc i) = true) ∧
      (oeffentlich (β.lokal (pc - zurueck) 0) = true →
        oeffentlich (β.lokal pc 0) = true) :=
  ⟨.alleOeffentlich, 0, alleOeffentlich_lokal 0 0,
    fun s _ => alleOeffentlich_temp 0 s, fun i _ _ => alleOeffentlich_lokal 0 i,
    fun _ => alleOeffentlich_lokal 0 0⟩

end Gabbro.Core.Ast.Semantik
