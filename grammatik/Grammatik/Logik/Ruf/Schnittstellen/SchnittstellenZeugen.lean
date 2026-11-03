module

public import Grammatik.Logik.Ruf.Schnittstellen.Zeuge
public import Grammatik.Nebenlaeufigkeit.Allgemein.MehrfadenZeuge.Teil1Basis

public section
namespace Gabbro.Grammatik.C06

-- Both admitted targets, the nontrivial interface and the concrete return
-- are supplied by the same fixture; none of these proofs assumes a duty.
theorem ptrPost_prefix_zeuge :
    (prog.ptrVertrag 0).postHolds entry later arguments ⟨3, by decide, by decide⟩ :=
  ptrPost_prefix (n := 0) prog entry later entry later arguments ⟨3, by decide, by decide⟩
    (by rfl)
    ⟨fun _ h => nomatch h, fun _ h => nomatch h⟩
    ⟨fun _ h => nomatch h, fun _ h => nomatch h⟩

theorem ptrReq_prefix_stmt_zeuge :
    ReqAmEintritt prog true entry (umsig pointer.property arguments) := by
  have h := ptrReq_prefix_stmt refinement operand operands entry entry arguments
    rfl (GleichAuf.refl _ _) rfl
  exact h

theorem ptrEns_prefix_stmt_zeuge :
    (prog.ptrVertrag 0).postHolds entry later arguments ⟨3, by decide, by decide⟩ := by
  have h := ptrEns_prefix_stmt refinement operand operands entry entry arguments
    (by rfl) (GleichAuf.refl _ _) (by rfl) later later ⟨3, by decide, by decide⟩ (by rfl)
    (GleichAuf.refl _ _)
  exact h

theorem PtrRufPflicht.torRuf_zeuge :
    torRuf prog handler true entry (umsig pointer.property arguments) =
      handler true entry (umsig pointer.property arguments) := by
  have h := Gabbro.Grammatik.PtrRufPflicht.torRuf refinement handler
    (p := operand) (args := operands) (σ := entry) (ρ := arguments) rfl
  exact h

theorem PtrRufPflicht.ens_zeuge :
    (prog.ptrVertrag 0).postHolds entry later arguments ⟨3, by decide, by decide⟩ := by
  have h := Gabbro.Grammatik.PtrRufPflicht.ens refinement
    (p := operand) (args := operands) (σ := entry) (ρ := arguments)
    (by rfl) later ⟨3, by decide, by decide⟩ (by rfl)
  exact h

theorem PtrVerfeinert.ens_zeuge :
    (prog.ptrVertrag 0).postHolds entry later arguments
      (ptrResult pointer.property ⟨3, by decide, by decide⟩) :=
  Gabbro.Grammatik.PtrVerfeinert.ens refinement pointer entry later arguments
    ⟨3, by decide, by decide⟩ (by rfl) (by rfl)

end Gabbro.Grammatik.C06

namespace Gabbro.Grammatik.C06.Locked

-- Reuse the shared, guarded account of the concurrency fixture. All targets
-- have the same writing signature, including the admitted pointer target.
@[expose] def decl : Deklaration :=
  { mD with
    sigNr := fun _ => mSig [.int 0 100] [()] [.konto]
    passt := fun _ _ => true
    passt_ok := fun _ _ _ => SigPasst.refl _ _
    eigner_nie_erzeugt := fun _ _ _ _ h => by simp only [List.not_mem_nil] at h }

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
    RufPasst decl (vertragVon decl MFn.setze) (decl.sigNr 0) [.held ()] where
  hw := fun _ h => h
  hg := fun g => nomatch g
  hk := ⟨[], List.Perm.refl [], by simp only [List.nil_sublist]⟩
  hh := by
    intro L _
    cases L
    exact List.mem_cons_self
  hx := by
    intro L _ hn
    cases L
    exact absurd List.mem_cons_self hn
  hb := fun _ hc => nomatch hc
  ownerReady := OwnerFlow.escrowReady_of_empty _ _ _ _ rfl

theorem footprint : FussS prog locks (fun _ => false) MFn.setze := by
  constructor
  · intro c hc
    cases c with
    | inl t =>
        have ht : t = MTab.konto := by
          cases t <;> revert hc <;> decide
        subst t
        exact Or.inl rfl
    | inr g => nomatch g
  · intro c hc
    cases hc

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
  ptr_vertrag_stabil (n := 0) footprint permissions (by
    intro c hc
    cases c with
    | inl t => cases t <;> revert hc <;> decide
    | inr g => nomatch g)

end Gabbro.Grammatik.C06.Locked
