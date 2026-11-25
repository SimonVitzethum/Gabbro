module

public import Core.Ast.LowLevel.DeviceUnit
public import Core.Ast.Semantik.Arithmetik

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Gabbro.Core.Katalog Gabbro.Core.Maschine Gabbro.Core.Aussen
open Gabbro.Core.Ast
open Gabbro.Core.Text
open Gabbro.Core.Ast.LowLevel.Device (Binding Denotation Rule RegisterAccess Befugt Frame State Plan)
open Gabbro.Core.Ast.LowLevel (entryContext)

private def ntDevice : Binding Plattform.x86_64.katalog where
  handle := ⟨0, ⟨⟨.virtio, 0⟩, 0⟩, [.read, .write]⟩
  row := Plattform.x86_64.virtio
  selected := by
    simp only [Katalog.enthaelt, Plattform.katalog, Plattform.zeilen, Plattform.endpunkte,
      List.map_cons, List.mem_append, List.mem_cons, eq_self, or_true, true_or]
  described := rfl

private def ntOwner : Kontext := .faden 0

private def ntDest : Ast.Identifier :=
  ⟨['r'], ⟨'r', [], rfl, by
    unfold isNameStart isLetter
    left
    left
    constructor <;> decide, by
      intro a h
      cases h⟩⟩

private def ntState (phase : GeraetePhase) : State :=
  let boot : State :=
    Zustand.start (fun _ => { phases := fun o => if o = ntDevice.object then some phase else none })
      (fun _ => .laeuft) (fun _ => ⟨some ntOwner, .nutzer, (), fun _ => false, 0, false, []⟩)
      ⟨fun _ => true, fun _ => 0⟩ (fun _ => 0) (.leer (fun _ => 0))
  { boot with buchung := { boot.buchung with
      geraet := fun o => if o = ntDevice.object then some (ntOwner, .frei) else none
      aussengriff := fun c h right => c = ntOwner ∧ h = ntDevice.handle ∧ right ∈ h.rights } }

private theorem ntBefugt :
    Befugt ntDevice .ready (.read 0x70) (ntState .ready) ntOwner := by
  refine ⟨rfl, rfl, ?_, rfl⟩
  intro z inAccess
  change z ∈ [⟨ntDevice.handle, .read⟩] at inAccess
  cases List.mem_singleton.mp inAccess
  refine ⟨rfl, rfl, ?_⟩
  exact List.mem_cons_self

/-- The device form is not vacuous: the declared virtio register issues a step. -/
def geraeteNI_nichtTrivialAussage : Prop :=
  ∃ (k : Katalog) (scope : Ast.Scope) (locals : Ast.Umgebung scope)
    (d : Denotation k scope) (c : Kontext) (s : State) (w : PUnit)
    (plans : List Plan) (u : State),
    ((d.unit locals).system.regel ()).impl c s w plans u

theorem geraeteNI_nichtTrivial : geraeteNI_nichtTrivialAussage :=
  ⟨Plattform.x86_64.katalog, [], leereUmgebung, .read ntDest ntDevice 0x70,
    ntOwner, ntState .ready, (), _, _,
    ⟨_, rfl, .issue ntBefugt rfl⟩⟩

end Gabbro.Core.Beobachtung
