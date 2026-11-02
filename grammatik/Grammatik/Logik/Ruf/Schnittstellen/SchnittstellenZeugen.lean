module

public import Grammatik.Logik.Ruf.Schnittstellen.Zeuge
public import Grammatik.Nebenlaeufigkeit.Allgemein.MehrfadenZeuge.Teil1Basis

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

namespace Gabbro.Grammatik.C06.Locked

-- Reuse the shared, guarded account of the concurrency fixture. All targets
-- have the same writing signature, including the admitted pointer target.
@[expose] def decl : Deklaration :=
  { mD with
    sigNr := fun _ => mSig [.int 0 100] [()] [.konto]
    passt := fun _ _ => true
    passt_ok := fun _ _ _ => SigPasst.refl _ _ }

@[expose] def predicate {Γ : Ctx} : Expr decl Γ [.held ()] .bool :=
  .eq (.slot .konto () (.widen (by decide) (by decide) (.lit 0))
    (by decide)) (.lit 0)

@[expose] def prog : Programm decl where
  invariante := fun _ => .tru
  requires := fun _ => predicate
  ensures := fun _ => predicate
  rumpf := fun _ => .ret .empty (List.Perm.refl _)
  ptrVertrag := fun _ => { pre := predicate, post := predicate }

@[expose] def pointer : Wert decl (.fnptr 0) := ⟨MFn.setze, rfl⟩

@[expose] def locks : SperrInv decl :=
  ⟨fun _ => [.inl .konto], fun _ s => decide ((s.slots .konto 0 ()).n = 0)⟩

theorem permissions :
    RufPasst decl (vertragVon decl MFn.setze) (decl.sigNr 0) [.held ()] := by
  refine { hw := fun _ h => h, hg := fun g => nomatch g,
    hk := ⟨[], List.Perm.refl [], by decide⟩,
    hh := by decide, hx := by decide }

theorem footprint : FussS prog locks (fun _ => false) MFn.setze := by
  constructor
  · intro c hc
    cases c with
    | inl t => cases t <;> decide
    | inr g => nomatch g
  · decide

-- The guarded carrier really occurs, the signature writes it, and the
-- pointer denotes an admitted target; no empty footprint discharges this.
theorem nondegenerate :
    (prog.ptrVertrag 0).pre.orte = [.inl MTab.konto] ∧
    (prog.ptrVertrag 0).post.orte = [.inl MTab.konto] ∧
    (decl.sigNr 0).schreibt .konto = true ∧
    Bewacht (D := decl) (.inl MTab.konto) () ∧
    pointer.val = MFn.setze := by
  decide

theorem ptr_vertrag_darf_zeuge : () ∈ (decl.sigNr 0).haelt :=
  ptr_vertrag_darf prog 0 (.inl MTab.konto) (by decide) () (by decide)

theorem ptr_vertrag_stabil_zeuge :
    (prog.ptrVertrag 0).pre.orte ++ (prog.ptrVertrag 0).post.orte ⊆
      stabilS prog locks (fun _ => false) MFn.setze [.held ()] :=
  ptr_vertrag_stabil footprint permissions (by decide)

end Gabbro.Grammatik.C06.Locked
