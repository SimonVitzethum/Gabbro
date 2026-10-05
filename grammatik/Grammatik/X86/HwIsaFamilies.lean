/-
  File:      Grammatik/X86/HwIsaFamilies.lean
  Subject:   ISA-strand families (compact/core/cond) on the coherent machine.

  Lane 1141: the ISA strand (`ISA.lean` `Instr`/`stepI`) is imported by NO
  coherent-machine module. This file plugs it into `HwMaschine`
  (`HardwareExecution.lean`) as a `HwAdapter`: the register path lifts
  the accepted `stepI` for memory-unchanged forms only, memory forms go
  through the accepted TSO byte events, and anything else refuses.
  Provenance (headings only, never silicon proofs): Intel SDM
  325462-093US, clone-local `intel-instruction-reference.txt`
  (MOV Vol. 2B 4-28, LEA Vol. 2A 3-547, NOT Vol. 2B 4-161,
  NEG Vol. 2B 4-158, TEST Vol. 2B 4-721, JMP Vol. 2A 3-504,
  ADD Vol. 2A 3-14).
-/
import Grammatik.X86.HardwareExecution
import Grammatik.X86.ISA
import Grammatik.X86.ExtendedExecution
import Grammatik.X86.ISAWitnesses

namespace Gabbro.Grammatik.X86

/-- Events of one ISA-strand step on the coherent machine: register
    execution of a decoded unified instruction, one observed byte load,
    one issued byte store, or explicit refusal. -/
inductive IsaEreignis where
  | reg : InstrDecoded → IsaEreignis
  | lade : Adresse → Byte → IsaEreignis
  | gibAus : Adresse → Byte → IsaEreignis
  | verweigert : IsaEreignis
  deriving DecidableEq, Repr

/-- Re-embed a `Zustand` successor: register file, flags and RIP move;
    machine memory, buffers, profiles, XMM and FP context stay. -/
def setKernVonZustand (m : HwMaschine) (c : Nat) (s' : Zustand) : HwMaschine :=
  setKernDaten m c ⟨s'.register, s'.flags, s'.rip,
    (m.kerne c).xmm, (m.kerne c).fp⟩

/-- Re-embedding a successor preserves well-formedness. -/
theorem setKernVonZustand_wf (m : HwMaschine) (c : Nat) (s' : Zustand)
    (h : HwWf m) : HwWf (setKernVonZustand m c s') :=
  setKernDaten_wf m c _ h

/-! ## 1. Register-path admission: which ISA forms never touch memory.

  The coherent register path (`HwSchritt.reg`) admits a step only where
  the successor leaves canonical memory alone. The classifier below
  names exactly the memory-touching forms -- pilot loads, stores and
  stack/control words, the narrow store, and the compact displaced
  loads/stores -- so they are refused on the register path and must
  use the TSO byte events instead. -/

/-- Register-path admission: `false` for every form whose accepted
    step can read or write canonical memory. -/
def isaNurRegister : Instr → Bool
  | .pilot (.load64 _ _ _) => false
  | .pilot (.store64 _ _ _) => false
  | .pilot (.push64 _) => false
  | .pilot (.pop64 _) => false
  | .pilot (.call32 _) => false
  | .pilot .ret => false
  | .narrow (.store32 _ _ _) => false
  | .compact (.load64Disp8 _ _ _) => false
  | .compact (.store64Disp8 _ _ _) => false
  | .compact (.load64Disp0 _ _) => false
  | .compact (.store64Disp0 _ _) => false
  | _ => true

/-- Pilot frame: every admitted pilot form keeps canonical memory,
    by the accepted per-form `schritt_*_speicher` lemmas. -/
theorem stepI_pilot_speicher (b : Befehl) (l : Nat) (s s' : Zustand)
    (hg : isaNurRegister (.pilot b) = true)
    (h : stepI ⟨.pilot b, l⟩ s = some s') : s'.speicher = s.speicher := by
  have hok : laengeOk l = true := by
    cases hlaenge : laengeOk l with
    | true => rfl
    | false => simp [stepI, schritt, hlaenge] at h
  rw [stepI_pilot] at h
  cases b with
  | movImm64 dst v =>
    exact schritt_movImm64_speicher ⟨.movImm64 dst v, l⟩ s s' dst v hok rfl h
  | movReg64 dst src =>
    exact schritt_movReg64_speicher ⟨.movReg64 dst src, l⟩ s s' dst src
      hok rfl h
  | addReg64 dst src =>
    exact schritt_addReg64_speicher ⟨.addReg64 dst src, l⟩ s s' dst src
      hok rfl h
  | subReg64 dst src =>
    exact schritt_subReg64_speicher ⟨.subReg64 dst src, l⟩ s s' dst src
      hok rfl h
  | xorReg64 dst src =>
    exact schritt_xorReg64_speicher ⟨.xorReg64 dst src, l⟩ s s' dst src
      hok rfl h
  | cmpReg64 lhs rhs =>
    exact schritt_cmpReg64_speicher ⟨.cmpReg64 lhs rhs, l⟩ s s' lhs rhs
      hok rfl h
  | load64 dst base disp =>
    have hcon : isaNurRegister (.pilot (.load64 dst base disp)) = false := rfl
    rw [hcon] at hg
    exact Bool.noConfusion hg
  | store64 base src disp =>
    have hcon : isaNurRegister (.pilot (.store64 base src disp)) = false := rfl
    rw [hcon] at hg
    exact Bool.noConfusion hg
  | jump32 disp =>
    exact schritt_jump32_speicher ⟨.jump32 disp, l⟩ s s' disp hok rfl h
  | jumpIf32 cond disp =>
    cases hfb : bedingung cond s.flags with
    | true =>
      exact schritt_jumpIf32_genommen_speicher ⟨.jumpIf32 cond disp, l⟩ s s'
        cond disp hok rfl hfb h
    | false =>
      exact schritt_jumpIf32_nicht_speicher ⟨.jumpIf32 cond disp, l⟩ s s'
        cond disp hok rfl hfb h
  | call32 disp =>
    have hcon : isaNurRegister (.pilot (.call32 disp)) = false := rfl
    rw [hcon] at hg
    exact Bool.noConfusion hg
  | push64 src =>
    have hcon : isaNurRegister (.pilot (.push64 src)) = false := rfl
    rw [hcon] at hg
    exact Bool.noConfusion hg
  | pop64 dst =>
    have hcon : isaNurRegister (.pilot (.pop64 dst)) = false := rfl
    rw [hcon] at hg
    exact Bool.noConfusion hg
  | ret =>
    have hcon : isaNurRegister (.pilot .ret) = false := rfl
    rw [hcon] at hg
    exact Bool.noConfusion hg

/-- Length refusal of one mul/div step, in `stepI` clothing. -/
theorem stepI_muldiv_laenge (b : MulDivBefehl) (l : Nat) (s : Zustand)
    (hfalse : laengeOk l = false) : stepI ⟨.muldiv b, l⟩ s = none := by
  rw [stepI_muldiv, md_laenge_misslungen ⟨b, l⟩ s hfalse]
  rfl

/-- Mul/div frame: all four forms are register-only; the trap and the
    bad-length refusal have no successor, by the accepted `md_*`
    equations. -/
theorem stepI_muldiv_speicher (b : MulDivBefehl) (l : Nat) (s s' : Zustand)
    (h : stepI ⟨.muldiv b, l⟩ s = some s') : s'.speicher = s.speicher := by
  rw [stepI_muldiv] at h
  cases b with
  | mulRax src =>
    by_cases hok : laengeOk l = true
    · have e := md_mul_erfolg ⟨.mulRax src, l⟩ s src hok rfl
      rw [e] at h
      simp [MulDivErgebnis.nachfolger] at h
      subst h
      rfl
    · have hfalse : laengeOk l = false := by
        cases hll : laengeOk l with
        | true => exact absurd hll hok
        | false => rfl
      have e := md_laenge_misslungen ⟨.mulRax src, l⟩ s hfalse
      rw [e] at h
      simp [MulDivErgebnis.nachfolger] at h
  | imul2 dst src =>
    by_cases hok : laengeOk l = true
    · have e := md_imul_erfolg ⟨.imul2 dst src, l⟩ s dst src hok rfl
      rw [e] at h
      simp [MulDivErgebnis.nachfolger] at h
      subst h
      rfl
    · have hfalse : laengeOk l = false := by
        cases hll : laengeOk l with
        | true => exact absurd hll hok
        | false => rfl
      have e := md_laenge_misslungen ⟨.imul2 dst src, l⟩ s hfalse
      rw [e] at h
      simp [MulDivErgebnis.nachfolger] at h
  | divRax src =>
    by_cases hok : laengeOk l = true
    · cases hqr : divWeitU (s.register .rdx) (s.register .rax)
          (s.register src) with
      | some qr =>
        obtain ⟨q, r⟩ := qr
        have e := md_div_erfolg ⟨.divRax src, l⟩ s src q r hok rfl hqr
        rw [e] at h
        simp [MulDivErgebnis.nachfolger] at h
        subst h
        rfl
      | none =>
        have e := md_div_halt ⟨.divRax src, l⟩ s src hok rfl hqr
        rw [e] at h
        simp [MulDivErgebnis.nachfolger] at h
    · have hfalse : laengeOk l = false := by
        cases hll : laengeOk l with
        | true => exact absurd hll hok
        | false => rfl
      have e := md_laenge_misslungen ⟨.divRax src, l⟩ s hfalse
      rw [e] at h
      simp [MulDivErgebnis.nachfolger] at h
  | idivRax src =>
    by_cases hok : laengeOk l = true
    · cases hqr : divWeitS (s.register .rdx) (s.register .rax)
          (s.register src) with
      | some qr =>
        obtain ⟨q, r⟩ := qr
        have e := md_idiv_erfolg ⟨.idivRax src, l⟩ s src q r hok rfl hqr
        rw [e] at h
        simp [MulDivErgebnis.nachfolger] at h
        subst h
        rfl
      | none =>
        have e := md_idiv_halt ⟨.idivRax src, l⟩ s src hok rfl hqr
        rw [e] at h
        simp [MulDivErgebnis.nachfolger] at h
    · have hfalse : laengeOk l = false := by
        cases hll : laengeOk l with
        | true => exact absurd hll hok
        | false => rfl
      have e := md_laenge_misslungen ⟨.idivRax src, l⟩ s hfalse
      rw [e] at h
      simp [MulDivErgebnis.nachfolger] at h

/-- Shift frame: every shift form is register-only, by the accepted
    `shiftSchritt_speicher` (no length premise needed there). -/
theorem stepI_shift_speicher (f : ShiftForm) (l : Nat) (s s' : Zustand)
    (h : stepI ⟨.shift f, l⟩ s = some s') : s'.speicher = s.speicher := by
  rw [stepI_shift] at h
  exact shiftSchritt_speicher ⟨f, l⟩ s s' h

/-- Narrow frame: the three register forms keep canonical memory, by
    the accepted narrow step equations; the store is refused here. -/
theorem stepI_narrow_speicher (o : NarrowOp) (l : Nat) (s s' : Zustand)
    (hg : isaNurRegister (.narrow o) = true)
    (h : stepI ⟨.narrow o, l⟩ s = some s') : s'.speicher = s.speicher := by
  have hok : laengeOk l = true := by
    cases hlaenge : laengeOk l with
    | true => rfl
    | false =>
      have hnone : stepNarrow (⟨o, l⟩ : NarrowDec) s = none := by
        simp [stepNarrow, hlaenge]
      rw [stepI_narrow] at h
      rw [hnone] at h
      cases h
  rw [stepI_narrow] at h
  cases o with
  | mov32rr dst src =>
    have e := stepNarrow_mov32 ⟨.mov32rr dst src, l⟩ s dst src hok rfl
    rw [e] at h
    cases h
    exact moveNarrow_memory s .b32 dst src
  | movzx8 dst src =>
    have e := stepNarrow_movzx8 ⟨.movzx8 dst src, l⟩ s dst src hok rfl
    rw [e] at h
    cases h
    rfl
  | movsx8 dst src =>
    have e := stepNarrow_movsx8 ⟨.movsx8 dst src, l⟩ s dst src hok rfl
    rw [e] at h
    cases h
    rfl
  | store32 base src disp =>
    have hcon : isaNurRegister (.narrow (.store32 base src disp)) = false :=
      rfl
    rw [hcon] at hg
    exact Bool.noConfusion hg

/-- Conditional-select frame: SETcc and CMOVcc never read or write
    memory, by the accepted `setCCAnwenden`/`cmovAnwenden` frames. -/
theorem stepI_cond_speicher (c : CondForm) (l : Nat) (s s' : Zustand)
    (h : stepI ⟨.cond c, l⟩ s = some s') : s'.speicher = s.speicher := by
  cases c with
  | setcc cond dst =>
    have hok : laengeOk l = true := by
      cases hlaenge : laengeOk l with
      | true => rfl
      | false =>
        have hnone : setccSchrittBytes l s dst cond = none := by
          simp [setccSchrittBytes, hlaenge]
        rw [stepI_setcc] at h
        rw [hnone] at h
        cases h
    rw [stepI_setcc] at h
    have e : setccSchrittBytes l s dst cond =
        some ({ setCCAnwenden s dst cond with rip := ripNach s.rip l }) := by
      simp [setccSchrittBytes, hok]
    rw [e] at h
    cases h
    exact setCCAnwenden_speicher s dst cond
  | cmov cond dst src =>
    have hok : laengeOk l = true := by
      cases hlaenge : laengeOk l with
      | true => rfl
      | false =>
        have hnone : cmovSchrittBytes l s dst src cond = none := by
          simp [cmovSchrittBytes, hlaenge]
        rw [stepI_cmov] at h
        rw [hnone] at h
        cases h
    rw [stepI_cmov] at h
    have e : cmovSchrittBytes l s dst src cond =
        some ({ cmovAnwenden s dst src cond with rip := ripNach s.rip l }) := by
      simp [cmovSchrittBytes, hok]
    rw [e] at h
    cases h
    exact cmovAnwenden_speicher s dst src cond

/-- Compact frame: the six non-memory forms keep canonical memory.
    Each successor is a register write or a RIP/flags update, so the
    memory projection is definitional; the four displaced loads and
    stores are refused here. -/
theorem stepI_kompakt_speicher (c : CompactBefehl) (l : Nat) (s s' : Zustand)
    (hg : isaNurRegister (.compact c) = true)
    (h : stepI ⟨.compact c, l⟩ s = some s') : s'.speicher = s.speicher := by
  have hok : laengeOk l = true := by
    cases hlaenge : laengeOk l with
    | true => rfl
    | false =>
      have hnone : schrittC (⟨c, l⟩ : CompactDecodiert) s = none := by
        simp [schrittC, hlaenge]
      rw [stepI_compact] at h
      rw [hnone] at h
      cases h
  rw [stepI_compact] at h
  cases c with
  | movImm32Zx dst imm =>
    have e : schrittC (⟨.movImm32Zx dst imm, l⟩ : CompactDecodiert) s =
        some (schrittRegister s (ripNach s.rip l) s.flags dst
          (zextWort32 imm)) := by
      simp [schrittC, hok]
    rw [e] at h
    cases h
    exact schrittRegister_speicher _ _ _ _ _
  | movImm32Sx dst imm =>
    have e : schrittC (⟨.movImm32Sx dst imm, l⟩ : CompactDecodiert) s =
        some (schrittRegister s (ripNach s.rip l) s.flags dst
          (dispWort imm)) := by
      simp [schrittC, hok]
    rw [e] at h
    cases h
    exact schrittRegister_speicher _ _ _ _ _
  | aluImm8 op dst imm =>
    cases hop : aluSchreibt op with
    | true =>
      have e : schrittC (⟨.aluImm8 op dst imm, l⟩ : CompactDecodiert) s =
          some (schrittRegister s (ripNach s.rip l)
            (aluFlags op (s.register dst) (kompaktDispWort8 imm)) dst
            (aluWert op (s.register dst) (kompaktDispWort8 imm))) := by
        simp [schrittC, hok, hop]
      rw [e] at h
      cases h
      exact schrittRegister_speicher _ _ _ _ _
    | false =>
      have e : schrittC (⟨.aluImm8 op dst imm, l⟩ : CompactDecodiert) s = some ({ s with rip := ripNach s.rip l, flags := aluFlags op (s.register dst) (kompaktDispWort8 imm) }) := by
        simp [schrittC, hok, hop]
      rw [e] at h
      cases h
      rfl
  | aluImm32 op dst imm =>
    cases hop : aluSchreibt op with
    | true =>
      have e : schrittC (⟨.aluImm32 op dst imm, l⟩ : CompactDecodiert) s =
          some (schrittRegister s (ripNach s.rip l)
            (aluFlags op (s.register dst) (dispWort imm)) dst
            (aluWert op (s.register dst) (dispWort imm))) := by
        simp [schrittC, hok, hop]
      rw [e] at h
      cases h
      exact schrittRegister_speicher _ _ _ _ _
    | false =>
      have e : schrittC (⟨.aluImm32 op dst imm, l⟩ : CompactDecodiert) s = some ({ s with rip := ripNach s.rip l, flags := aluFlags op (s.register dst) (dispWort imm) }) := by
        simp [schrittC, hok, hop]
      rw [e] at h
      cases h
      rfl
  | load64Disp8 dst base disp =>
    have hcon : isaNurRegister
        (.compact (.load64Disp8 dst base disp)) = false := rfl
    rw [hcon] at hg
    exact Bool.noConfusion hg
  | store64Disp8 base src disp =>
    have hcon : isaNurRegister
        (.compact (.store64Disp8 base src disp)) = false := rfl
    rw [hcon] at hg
    exact Bool.noConfusion hg
  | load64Disp0 dst base =>
    have hcon : isaNurRegister
        (.compact (.load64Disp0 dst base)) = false := rfl
    rw [hcon] at hg
    exact Bool.noConfusion hg
  | store64Disp0 base src =>
    have hcon : isaNurRegister
        (.compact (.store64Disp0 base src)) = false := rfl
    rw [hcon] at hg
    exact Bool.noConfusion hg
  | jump8 rel =>
    have e : schrittC (⟨.jump8 rel, l⟩ : CompactDecodiert) s =
        some ({ s with rip := ripNach s.rip l + kompaktDispWort8 rel }) := by
      simp [schrittC, hok]
    rw [e] at h
    cases h
    rfl
  | jumpIf8 cond rel =>
    have e : schrittC (⟨.jumpIf8 cond rel, l⟩ : CompactDecodiert) s = some ({ s with rip := (if bedingung cond s.flags then ripNach s.rip l + kompaktDispWort8 rel else ripNach s.rip l) }) := by
      simp [schrittC, hok]
    rw [e] at h
    cases h
    rfl

/-- Register-path frame over the whole strand: every admitted ISA form
    keeps canonical memory. The old evaluators are lifted, never
    redefined. -/
theorem stepI_nurRegister_speicher (d : InstrDecoded) (s s' : Zustand)
    (hg : isaNurRegister d.instr = true)
    (h : stepI d s = some s') : s'.speicher = s.speicher := by
  obtain ⟨i, l⟩ := d
  cases i with
  | pilot b => exact stepI_pilot_speicher b l s s' hg h
  | muldiv b => exact stepI_muldiv_speicher b l s s' h
  | shift f => exact stepI_shift_speicher f l s s' h
  | narrow o => exact stepI_narrow_speicher o l s s' hg h
  | cond c => exact stepI_cond_speicher c l s s' h
  | compact c => exact stepI_kompakt_speicher c l s s' hg h
  | core c =>
    have e : stepI ⟨.core c, l⟩ s = coreSchritt ⟨c, l⟩ s :=
      stepI_core c l s
    rw [e] at h
    exact coreSchritt_speicher ⟨c, l⟩ s s' h

/- CUTS:
    Skeleton only: the event type and the re-embedding. The classifier,
    the adapter, the stepI/stepExt agreement, the refusals and the
    two-core witness are OPEN.
-/

#print axioms setKernVonZustand_wf

end Gabbro.Grammatik.X86
