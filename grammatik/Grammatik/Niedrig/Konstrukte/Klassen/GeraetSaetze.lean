module

public import Grammatik.Niedrig.Konstrukte.Klassen.Geraet

@[expose] public section

namespace Gabbro.Grammatik.LowLevel.Construct

variable {D : Deklaration}

theorem mmioReadStep_promised (oracle : Orakel D) (view : View D) (layout : AdressLayout D)
    (register : D.Reg) (binding : MmioRegister D register)
    (checked : MmioReadOk view layout register binding) (fallible : Bool) (world : World D)
    (value : Wert D (D.rtyp register))
    (decoded : einpassen oracle.zeiger (D.rtyp register)
      (oracle.regLies register (world.fragt (.inr (.inl register)))) = some value)
    (promised : D.rzusage register value = true) :
    (mmioReadStep oracle view layout register binding checked fallible world).value = .ok (.ok value) := by
  simp only [mmioReadStep, decoded, promised, ↓reduceIte]

theorem mmioReadStep_reason (oracle : Orakel D) (view : View D) (layout : AdressLayout D)
    (register : D.Reg) (binding : MmioRegister D register)
    (checked : MmioReadOk view layout register binding) (world : World D)
    (value : Wert D (D.rtyp register))
    (decoded : einpassen oracle.zeiger (D.rtyp register)
      (oracle.regLies register (world.fragt (.inr (.inl register)))) = some value)
    (broken : D.rzusage register value = false) :
    (mmioReadStep oracle view layout register binding checked true world).value = .ok (.error value) ∧
    (mmioReadStep oracle view layout register binding checked false world).value = .error (.geraet register) := by
  constructor <;> simp only [mmioReadStep, decoded, broken, Bool.false_eq_true, ↓reduceIte]

theorem mmioReadStep_event (oracle : Orakel D) (view : View D) (layout : AdressLayout D)
    (register : D.Reg) (binding : MmioRegister D register)
    (checked : MmioReadOk view layout register binding) (fallible : Bool) (world : World D) :
    (mmioReadStep oracle view layout register binding checked fallible world).event.order = binding.readOrder ∧
    (mmioReadStep oracle view layout register binding checked fallible world).event.binding.bytes = binding.bytes ∧
    (mmioReadStep oracle view layout register binding checked fallible world).world.spur =
      .fremd (.inr (.inl register)) :: world.spur := ⟨rfl, rfl, rfl⟩

theorem mmioReadStep_gut (oracle : Orakel D) (view : View D) (layout : AdressLayout D)
    (register : D.Reg) (binding : MmioRegister D register)
    (checked : MmioReadOk view layout register binding) (fallible : Bool) (world : World D)
    (writes : D.Tab → Bool) (globals : D.Glob → Bool) :
    Gut writes globals world (mmioReadStep oracle view layout register binding checked fallible world).world :=
  gut_fragt world (.inr (.inl register))

theorem mmioWriteStep_confined {view : View D} {layout : AdressLayout D} {register : D.Reg}
    {binding : MmioRegister D register} (checked : MmioWriteOk view layout register binding)
    (offset : Nat) (within : offset < binding.bytes) :
    view.Contains (binding.backing, binding.address + offset) := by
  obtain ⟨_, _, _, backing, _, _, low, high, _⟩ := checked.1
  exact ⟨backing.symm, by omega, by omega⟩

theorem mmioWriteStep_event (oracle : Orakel D) (view : View D) (layout : AdressLayout D)
    (register : D.Reg) (binding : MmioRegister D register)
    (checked : MmioWriteOk view layout register binding) (value : Wert D (D.rtyp register)) (world : World D) :
    (mmioWriteStep oracle view layout register binding checked value world).event.order = binding.writeOrder ∧
    (mmioWriteStep oracle view layout register binding checked value world).event.raw = roh value ∧
    (mmioWriteStep oracle view layout register binding checked value world).world = world := ⟨rfl, rfl, rfl⟩

end Gabbro.Grammatik.LowLevel.Construct
