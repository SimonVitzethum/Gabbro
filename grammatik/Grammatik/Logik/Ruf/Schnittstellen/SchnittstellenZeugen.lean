module

public import Grammatik.Logik.Ruf.Schnittstellen.Zeuge

public section
namespace Gabbro.Grammatik.C06

-- Both admitted targets, the nontrivial interface and the concrete return
-- are supplied by the same fixture; none of these proofs assumes a duty.
theorem ptrPost_prefix_zeuge :
    (prog.ptrVertrag 0).postHolds entry later arguments ⟨3, by decide, by decide⟩ :=
  ptrPost_prefix prog entry later entry later arguments ⟨3, by decide, by decide⟩
    rfl (by intro o h; cases h) (by intro o h; cases h)

theorem ptrReq_prefix_stmt_zeuge :
    ReqAmEintritt prog true entry (umsig pointer.property arguments) := by
  have h := ptrReq_prefix_stmt refinement operand operands entry entry arguments
    rfl (GleichAuf.refl _ _)
  simpa using h

theorem ptrEns_prefix_stmt_zeuge :
    (prog.ptrVertrag 0).postHolds entry later arguments ⟨3, by decide, by decide⟩ := by
  have h := ptrEns_prefix_stmt refinement operand operands entry entry arguments
    rfl (GleichAuf.refl _ _) later later ⟨3, by decide, by decide⟩ rfl
    (GleichAuf.refl _ _)
  simpa using h

theorem PtrRufPflicht.torRuf_zeuge :
    torRuf prog handler true entry (umsig pointer.property arguments) =
      handler true entry (umsig pointer.property arguments) := by
  have h := Gabbro.Grammatik.PtrRufPflicht.torRuf refinement handler
    (p := operand) (args := operands) (σ := entry) (ρ := arguments) rfl
  simpa using h

theorem PtrRufPflicht.ens_zeuge :
    (prog.ptrVertrag 0).postHolds entry later arguments ⟨3, by decide, by decide⟩ := by
  have h := Gabbro.Grammatik.PtrRufPflicht.ens refinement
    (p := operand) (args := operands) (σ := entry) (ρ := arguments)
    rfl later ⟨3, by decide, by decide⟩ rfl
  simpa using h

theorem PtrVerfeinert.ens_zeuge :
    (prog.ptrVertrag 0).postHolds entry later arguments
      (ptrResult pointer.property ⟨3, by decide, by decide⟩) :=
  Gabbro.Grammatik.PtrVerfeinert.ens refinement pointer entry later arguments
    ⟨3, by decide, by decide⟩ rfl rfl

end Gabbro.Grammatik.C06
