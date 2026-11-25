/-
  File:      core/Core/Aussen/Frage/Form.lean
  Subject:   THE PROGRAM FORMS OF OUTSIDE QUESTIONS (MK-06, design). A program issues an
             outside question and consumes its answer as two command forms: `frage` names the
             operation and its argument slots and binds the answer, `verbrauche` takes the next
             arrived answer of the acting context. Catalogue services (`Decl.environment` calls)
             are a call-site shape `Dienstruf`: the selected firmware row with its ABI, service
             and payload, mapped to one `firmware` question. Float operations are a hardware-row
             question `GleitAnfrage` over bits (`Ty.float32/64` as `UInt32`/`UInt64`); the value
             comes from the answer. An outside error is a reason exit `aussenEnde`.
             The implementer moves these shapes into `Befehl` (new constructors at the END),
             adds `Wirkungsklasse.verbrauche` at the END with its registry packet, appends
             `.float32`/`.float64` at the END of `Ty`, and threads `Rufstelle.dienst` through
             the call-site check; every arm the brief names (`Klasse`, `Schritt`, `Pflichten`,
             `Sicherheit`, `Beweise/*`, the `Waechter` registry) grows by the same pattern MK-07
             used for the lifecycle classes. This file only fixes the shapes, it proves nothing.
-/
module

public import Core.Katalog.Aussen
public import Core.Katalog.FirmwareNamen
public import Core.Katalog.Gleit
public import Core.Maschine.Ergebnis

@[expose] public section

namespace Gabbro.Core.Aussenfrage

open Gabbro.Core.Katalog
open Gabbro.Core.Maschine

/-- **The program forms of an outside question.** `frage` names the catalogue operation
    and its argument slots; the answer is bound at `ziel`. `verbrauche` takes the next
    arrived answer of the acting context (`Aktion.verbrauche`) and binds it at `ziel`.
    `frage` maps to `Wirkungsklasse.frage` and `Aktion.frage`; `verbrauche` maps to the
    new class `Wirkungsklasse.verbrauche` (END of the inductive) and `Aktion.verbrauche`.
    An outside object is read or copied with ONE atomic outside question: the form never
    names the same object twice, so there is no double fetch at the source level. -/
inductive Aussenfrageform where
  | frage (ziel : Nat) (operation : AussenOperation) (args : List Nat)
  | verbrauche (ziel : Nat)
  deriving DecidableEq, Repr

/-- **A catalogue-service call site** (`Rufstelle.dienst` shape). After `waehleUmgebung`
    selected the environment, the call names the firmware row with its ABI, the service of
    that row and the payload slots. The payload is marshalled to bytes by the elaborator;
    the checker rule for the row fixes which slots may flow into it. -/
structure Dienstruf where
  name : String
  abi : DienstAbi
  row : FirmwareZeile
  service : Dienst
  payload : List UInt8
  deriving DecidableEq, Repr

/-- A service call is one `firmware` question at the endpoint of its row, through a handle
    the context holds. Name resolution never happens here: only `resolve` answers a
    handle (`namen_nur_griff`). -/
def Dienstruf.frage (d : Dienstruf) (h : Handle) : Frage :=
  ⟨d.row.endpunkt, h, [], .firmware d.service d.payload⟩

/-- The endpoint of a service call is the endpoint of its row. -/
theorem Dienstruf.endpunkt (d : Dienstruf) (h : Handle) :
    (d.frage h).endpoint = d.row.endpunkt :=
  rfl

/-- **A float operation as a hardware-row question.** The operands are bits; the value
    comes from the answer (`GleitAntwort.bits` for arithmetic, `GleitAntwort.wahr` for
    comparisons). `Ty.float32` is `UInt32` bits, `Ty.float64` is `UInt64` bits; the
    implementer appends both constructors at the END of `Ty`. -/
inductive GleitAnfrage where
  | bin32 (op : GleitBinaer) (a b : UInt32)
  | sqrt32 (a : UInt32)
  | fma32 (a b c : UInt32)
  | vonInt32 (n : Int)
  | vergleich32 (op : GleitVergleich) (a b : UInt32)
  | bin64 (op : GleitBinaer) (a b : UInt64)
  | sqrt64 (a : UInt64)
  | fma64 (a b c : UInt64)
  | vonInt64 (n : Int)
  | vergleich64 (op : GleitVergleich) (a b : UInt64)
  deriving DecidableEq, Repr

/-- The 32-bit float questions as row questions; every other form maps to none. -/
def GleitAnfrage.zuFrage32 : GleitAnfrage → Option (GleitFrage UInt32)
  | .bin32 op a b => some (.binaer op a b)
  | .sqrt32 a => some (.sqrt a)
  | .fma32 a b c => some (.fma a b c)
  | .vonInt32 n => some (.vonInt n)
  | .vergleich32 op a b => some (.vergleich op a b)
  | .bin64 .. | .sqrt64 .. | .fma64 .. | .vonInt64 .. | .vergleich64 .. => none

/-- The 64-bit float questions as row questions; every other form maps to none. -/
def GleitAnfrage.zuFrage64 : GleitAnfrage → Option (GleitFrage UInt64)
  | .bin64 op a b => some (.binaer op a b)
  | .sqrt64 a => some (.sqrt a)
  | .fma64 a b c => some (.fma a b c)
  | .vonInt64 n => some (.vonInt n)
  | .vergleich64 op a b => some (.vergleich op a b)
  | .bin32 .. | .sqrt32 .. | .fma32 .. | .vonInt32 .. | .vergleich32 .. => none

/-- Every 32-bit form maps to a 32-bit row question. -/
theorem GleitAnfrage.form32 (g : GleitAnfrage) (h : g.zuFrage64 = none) :
    ∃ q : GleitFrage UInt32, g.zuFrage32 = some q := by
  cases g with
  | bin32 op a b => exact ⟨_, rfl⟩
  | sqrt32 a => exact ⟨_, rfl⟩
  | fma32 a b c => exact ⟨_, rfl⟩
  | vonInt32 n => exact ⟨_, rfl⟩
  | vergleich32 op a b => exact ⟨_, rfl⟩
  | bin64 op a b =>
    simp only [GleitAnfrage.zuFrage64] at h
    cases h
  | sqrt64 a =>
    simp only [GleitAnfrage.zuFrage64] at h
    cases h
  | fma64 a b c =>
    simp only [GleitAnfrage.zuFrage64] at h
    cases h
  | vonInt64 n =>
    simp only [GleitAnfrage.zuFrage64] at h
    cases h
  | vergleich64 op a b =>
    simp only [GleitAnfrage.zuFrage64] at h
    cases h

/-- Every 64-bit form maps to a 64-bit row question. -/
theorem GleitAnfrage.form64 (g : GleitAnfrage) (h : g.zuFrage32 = none) :
    ∃ q : GleitFrage UInt64, g.zuFrage64 = some q := by
  cases g with
  | bin32 op a b =>
    simp only [GleitAnfrage.zuFrage32] at h
    cases h
  | sqrt32 a =>
    simp only [GleitAnfrage.zuFrage32] at h
    cases h
  | fma32 a b c =>
    simp only [GleitAnfrage.zuFrage32] at h
    cases h
  | vonInt32 n =>
    simp only [GleitAnfrage.zuFrage32] at h
    cases h
  | vergleich32 op a b =>
    simp only [GleitAnfrage.zuFrage32] at h
    cases h
  | bin64 op a b => exact ⟨_, rfl⟩
  | sqrt64 a => exact ⟨_, rfl⟩
  | fma64 a b c => exact ⟨_, rfl⟩
  | vonInt64 n => exact ⟨_, rfl⟩
  | vergleich64 op a b => exact ⟨_, rfl⟩

/-- **An outside error is a reason exit.** Consuming an error answer ends the acting
    context with the error as its reason (`Ende.grund`), never with a value. The
    implementer threads this through `verbrauche`: an error answer takes the
    `beendet (.grund …)` shape of `Schrittform.faedenNach`, so joining it halts the
    joiner as `.verbinde` on a reason exit does. -/
def aussenEnde (e : AussenFehler) : Ende Int AussenFehler :=
  .grund e

end Gabbro.Core.Aussenfrage
