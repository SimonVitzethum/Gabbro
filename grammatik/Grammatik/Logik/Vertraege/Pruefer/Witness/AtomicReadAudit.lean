module

public import Grammatik.Gen.Zeugen.M.M49_50
public import Grammatik.Zielsatz.Atomar.AtomarAkzeptiert

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer.AtomicReadAudit

open Gabbro.Grammatik Gen Zielsatz

abbrev original := Gen.Zeugen.M49_50.e
abbrev declaration := original.D

local instance : DecidableEq declaration.Fn := original.aufz.decFn
local instance : DecidableEq declaration.Ax := original.aufz.decAx

/-- Both existing gates accept the unchanged generated candidate. -/
theorem gates_zeuge :
    Invarianten.Pruefer.programInvariantsB original.P original.S original.fs original.lockSources
      {} original.ls = true ∧
    KontrakteGeprueftB original.P original.S original.fs original.lockSources = true := by
  constructor <;> decide +kernel

/-- This is the generator's actual model Bool, not a substitute checker. -/
theorem accepted_zeuge : original.gueltig = true :=
  Gen.Zeugen.M49_50.e_gueltig_iff_gates.mpr gates_zeuge

#print axioms accepted_zeuge

/-- One planted fault: only the second function's postcondition changes. -/
def falseProgram : Programm declaration :=
  { original.P with ensures := fun f => if f.val = 1 then .fls else original.P.ensures f }

def negative : Einsatz :=
  { original with P := falseProgram, hBoden := original.hBoden }

theorem false_contract_refused_zeuge : negative.gueltig = false := by decide +kernel

abbrev returnedFunction : declaration.Fn := ⟨1, by decide⟩

/-- Every stored cell has Boolean type in this generated declaration. -/
def world : World declaration where
  slots
    | ⟨0, _⟩, _, ⟨0, _⟩ => false
    | ⟨1, _⟩, _, ⟨0, _⟩ => false
    | ⟨0, _⟩, _, ⟨n + 1, h⟩ => by have : n + 1 < 1 := h; omega
    | ⟨1, _⟩, _, ⟨n + 1, h⟩ => by have : n + 1 < 1 := h; omega
    | ⟨n + 2, h⟩, _, _ => by have : n + 2 < 2 := h; omega
  globs
    | ⟨0, _⟩ => false
    | ⟨1, _⟩ => false
    | ⟨2, _⟩ => false
    | ⟨3, _⟩ => false
    | ⟨n + 4, h⟩ => by have : n + 4 < 4 := h; omega
  spur := []

def calls (f : declaration.Fn) (_ : World declaration)
    (_ : Env declaration (declaration.params f)) : RufAusgang f := .logik .schleife

#print axioms false_contract_refused_zeuge

end Gabbro.Grammatik.Vertraege.Pruefer.AtomicReadAudit
