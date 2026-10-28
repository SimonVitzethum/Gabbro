import Grammatik.Code.Conc.GXStep
import Grammatik.Code.Conc.SharedWitness

/-
  File:      Grammatik/Code/Conc/GXWitness.lean
  Subject:   TRACK L, PHASE L3 -- A WITNESS of `stmt_gx`: a GX step of a statement, matched by thread-machine steps.

  The declaration of `Conc/Witness.lean` (one table with one slot, one SHARED atomic global) at the 64-bit target; two
  threads. Thread 0 stands at the entry of the lowering of `konto[0].v = 1`; thread 1 is finished. The shared atomic
  is the carrier machine GX presents freely: the machine's memory holds the global `5`, the PRESENTED memory `9`, and
  the successor memory `3`, while the IR memory holds `0` in the cell throughout. `stmt_gx` is instantiated: the
  machine reaches, with thread 0 moving alone, a state in which thread 0 is at the continuation, thread 1 is as it was,
  and the IR memory represents the successor memory (slot `1`, global free).
-/

namespace Gabbro.Code.Lower.WitC

open Gabbro.Grammatik

section C64

local instance confG64 : Conf := ⟨64, false, Or.inr rfl⟩

theorem cDarf (Λ : List (Res cD)) : darf cD () Λ := fun w hw => nomatch hw

/-- `konto[0].v = 1`. -/
def cS : Stmt (V := vC) cD false [] [] [] :=
  .assignSlot () ()
    (.widen (lo := 0) (hi := 0) (by decide) (by decide) (.lit 0))
    (.widen (lo := 1) (hi := 1) (by decide) (by decide) (.lit 1)) rfl (cDarf _)

def cLow2 : Option (List Block × St) := lowerS cLay [] (0, 0) cS 1 2 ⟨0, 3⟩

def cBlks2 : List Block := (cLow2.map Prod.fst).getD []

def cSt2 : St := (cLow2.map Prod.snd).getD ⟨0, 0⟩

theorem cLow2_eq : cLow2 = some (cBlks2, cSt2) := rfl

def cMod2 : Modl := ⟨[], [⟨"f", [], .void, ⟨0, [], [], .jmp 1⟩ :: cBlks2 ++ [⟨2, [], [], .ret none⟩]⟩]⟩

theorem cBlks2_length : cBlks2.length = 1 := by decide +kernel

theorem cIn2 : InM cMod2 0 cBlks2 := by
  intro b hb
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hb
  have h2 : i = 0 := by
    have := cBlks2_length
    omega
  subst h2
  rfl

theorem cFn2 : FnOk cLay cMod2 := fun f =>
  ⟨fun τ hτ => absurd hτ List.not_mem_nil, _, _, rfl, rfl, rfl, rfl, rfl⟩

theorem cCall2 : CallRef cLay cMod2 (Sees.shared cLay) cR :=
  ⟨fun _ _ _ _ _ h => (nomatch h), fun _ _ _ _ _ h => (nomatch h)⟩

/-- The shared atomic of the declaration, as a carrier of machine GX. -/
def cTg : cD.Tab ⊕ cD.Glob → Prop := fun c => c = .inr ()

theorem cTgShared : TgShared cLay cTg := fun c h => ⟨(), h, rfl⟩

/-- The thread table: thread 0 at the entry of the lowering of the statement, thread 1 finished. -/
def cTM : TM := ⟨mem0, fun v => if v = 0 then .run ⟨0, 1, 0, fun _ => none, none⟩ [] else .done none⟩

theorem cMem_wf' : WfL cLay cTM.m := cMem_wf

/-- **`stmt_gx` instantiated.** -/
theorem stmt_gx_zeuge (σ' : World cD) (ρ' : Env cD [])
    (hstep : execStmt cO 0 cR cS (Speicher.welt ⟨wld5.slots, fun _ => ⟨9, by decide, by decide⟩⟩ []) .nil =
      Ausgang.ok σ' ρ') :
    ∃ (T' : TM) (rs' : Regs), TReach cMod2 (Sees.shared cLay) cTM T' ∧
      T'.th 0 = .run ⟨0, 2, 0, rs', none⟩ [] ∧ T'.th 1 = cTM.th 1 ∧
      Rep cLay (Speicher.welt ⟨σ'.slots, fun _ => ⟨3, by decide, by decide⟩⟩ []) T'.m := by
  obtain ⟨T', rs', h1, h2, h3, h4, _⟩ := stmt_gx cLay cLayOk cTgShared [] (0, 0) cO 0 cR cS 1 2 ⟨0, 3⟩ cSt2 cBlks2
    cLow2_eq cMod2 (Sees.shared cLay) 0 cIn2 ⟨_, rfl, rfl⟩ ⟨⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩⟩ cFn2 cCall2 cTM 0
    (fun _ => none) [] none (by simp only [cTM, ↓reduceIte]) wld5.speicher ⟨wld5.slots, fun _ => ⟨9, by decide, by decide⟩⟩
    ⟨σ'.slots, fun _ => ⟨3, by decide, by decide⟩⟩ [] (rep_welt [] rep_free_witness) (fun c hc => by
      cases c with
      | inl t => rfl
      | inr g => exact absurd rfl hc) .nil trivial cMem_wf (fun x hx => absurd hx List.not_mem_nil) σ' ρ' hstep
    (fun c hc => by
      cases c with
      | inl t => rfl
      | inr g => exact absurd rfl hc)
  exact ⟨T', rs', h1, h2, h3 1 (by decide), h4⟩

/-- The premise is not vacuous: the statement does end normally on the presented memory. -/
theorem stmt_gx_premise : ∃ σ' ρ', execStmt cO 0 cR cS
    (Speicher.welt ⟨wld5.slots, fun _ => ⟨9, by decide, by decide⟩⟩ []) .nil = Ausgang.ok σ' ρ' := ⟨_, _, rfl⟩

end C64

end Gabbro.Code.Lower.WitC
