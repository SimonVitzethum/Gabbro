module
public import Grammatik.Code.Conc.GXStep
public import Grammatik.Code.Conc.ErfuellbarkeitShared
@[expose] public section


/-
  File:      Grammatik/Code/Conc/GXWitness.lean
  Subject:   Satisfiability of the premises of `stmt_gx` (stream E5; was the witness of track L, phase L3): a GX step of a statement, matched by thread-machine steps.

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

theorem cLow2_eq : cLow2 = some (cBlks2, cSt2) := by rfl

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

/-- **Satisfiability of the code-model premises** (stream E5): the layout is correct (`LayoutOk`), the shared
    carrier set is admissible (`TgShared`), the lowered module's functions are well formed (`FnOk`) and its
    calls resolved (`CallRef`), the IR memory is well laid out (`WfL`), and the statement ends normally on the
    presented memory -- the premises of `stmt_gx` hold jointly. -/
theorem stmt_gx_erfuellbar : LayoutOk cLay ∧ TgShared cLay cTg ∧ FnOk cLay cMod2 ∧
    CallRef cLay cMod2 (Sees.shared cLay) cR ∧ WfL cLay cTM.m ∧ InM cMod2 0 cBlks2 ∧ ∃ σ' ρ', execStmt cO 0 cR cS
    (Speicher.welt ⟨wld5.slots, fun _ => ⟨9, by decide, by decide⟩⟩ []) .nil = Ausgang.ok σ' ρ' :=
  ⟨cLayOk, cTgShared, cFn2, cCall2, cMem_wf, cIn2, _, _, rfl⟩

end C64

end Gabbro.Code.Lower.WitC
