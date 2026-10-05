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
import Grammatik.X86.Hw.Grundlage.HardwareExecution
import Grammatik.X86.Befehle.ISA.ISA
import Grammatik.X86.Hw.Grundlage.ExtendedExecution
import Grammatik.X86.Befehle.ISA.ISAWitnesses
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

/-! ## 2. The adapter: register lift plus TSO byte events.

  Memory forms never take the register path (the classifier refuses
  them there); they travel as buffered byte issues and byte loads,
  exactly the `HwSchritt` events of §3. No SC word effect is ever
  substituted for a buffered access. -/

/-- One ISA-strand step on the coherent machine: register execution
    of a decoded unified instruction (admitted forms only), one
    observed byte load, one issued byte store, or explicit refusal. -/
def adapterIsa : HwAdapter IsaEreignis :=
  ⟨fun m c e =>
    match e with
    | .reg d =>
      match stepI d (projZustand m c) with
      | some s' =>
        match isaNurRegister d.instr with
        | true => some (setKernVonZustand m c s')
        | false => none
      | none => none
    | .lade a v =>
      match loadByte (tsoAnsicht m) c a with
      | some w => if w == v then some m else none
      | none => none
    | .gibAus a v =>
      match issueByte (tsoAnsicht m) c a v with
      | some s' => some (setTso m s')
      | none => none
    | .verweigert => none⟩

/-- After re-embedding, the core projects to the successor register
    file over the shared memory. -/
theorem setKernVonZustand_register (m : HwMaschine) (c : Nat)
    (s' : Zustand) :
    ((setKernVonZustand m c s').kerne c).register = s'.register := by
  unfold setKernVonZustand setKernDaten
  simp

/-- After re-embedding, the core carries the successor flags. -/
theorem setKernVonZustand_flags (m : HwMaschine) (c : Nat)
    (s' : Zustand) :
    ((setKernVonZustand m c s').kerne c).flags = s'.flags := by
  unfold setKernVonZustand setKernDaten
  simp

/-- After re-embedding, the core carries the successor RIP. -/
theorem setKernVonZustand_rip (m : HwMaschine) (c : Nat)
    (s' : Zustand) :
    ((setKernVonZustand m c s').kerne c).rip = s'.rip := by
  unfold setKernVonZustand setKernDaten
  simp

/-- Re-embedding keeps the shared memory. -/
theorem setKernVonZustand_speicher (m : HwMaschine) (c : Nat)
    (s' : Zustand) : (setKernVonZustand m c s').mem = m.mem := rfl

/-- Re-embedding keeps the buffers. -/
theorem setKernVonZustand_puffer (m : HwMaschine) (c : Nat)
    (s' : Zustand) (d : Nat) :
    (setKernVonZustand m c s').puffer d = m.puffer d := rfl

/-- Selection: an admitted register step is taken. -/
theorem adapterIsa_reg (m : HwMaschine) (c : Nat) (d : InstrDecoded)
    (s' : Zustand)
    (hstep : stepI d (projZustand m c) = some s')
    (hg : isaNurRegister d.instr = true) :
    adapterIsa.schritt m c (.reg d) = some (setKernVonZustand m c s') := by
  simp only [adapterIsa, hstep, hg]

/-- Selection: a refused evaluation is adapter refusal. -/
theorem adapterIsa_reg_verweigert_schritt (m : HwMaschine) (c : Nat)
    (d : InstrDecoded)
    (hstep : stepI d (projZustand m c) = none) :
    adapterIsa.schritt m c (.reg d) = none := by
  simp only [adapterIsa, hstep]

/-- Selection: a memory form is refused on the register path. -/
theorem adapterIsa_reg_verweigert_speicher (m : HwMaschine) (c : Nat)
    (d : InstrDecoded) (s' : Zustand)
    (hstep : stepI d (projZustand m c) = some s')
    (hg : isaNurRegister d.instr = false) :
    adapterIsa.schritt m c (.reg d) = none := by
  simp only [adapterIsa, hstep, hg]

/-- Selection: an observed load is taken. -/
theorem adapterIsa_lade (m : HwMaschine) (c : Nat) (a : Adresse)
    (v w : Byte)
    (hload : loadByte (tsoAnsicht m) c a = some w)
    (heq : (w == v) = true) :
    adapterIsa.schritt m c (.lade a v) = some m := by
  simp only [adapterIsa, hload]
  exact if_pos heq

/-- Selection: a mismatched observation refuses. -/
theorem adapterIsa_lade_verweigert_wert (m : HwMaschine) (c : Nat)
    (a : Adresse) (v w : Byte)
    (hload : loadByte (tsoAnsicht m) c a = some w)
    (heq : (w == v) = false) :
    adapterIsa.schritt m c (.lade a v) = none := by
  simp only [adapterIsa, hload]
  exact if_neg (by simp [heq])

/-- Selection: an unreadable load refuses. -/
theorem adapterIsa_lade_verweigert (m : HwMaschine) (c : Nat)
    (a : Adresse) (v : Byte)
    (hload : loadByte (tsoAnsicht m) c a = none) :
    adapterIsa.schritt m c (.lade a v) = none := by
  simp only [adapterIsa, hload]

/-- Selection: a permitted issue is taken. -/
theorem adapterIsa_gibAus (m : HwMaschine) (c : Nat) (a : Adresse)
    (v : Byte) (s' : TSOZustand)
    (hissue : issueByte (tsoAnsicht m) c a v = some s') :
    adapterIsa.schritt m c (.gibAus a v) = some (setTso m s') := by
  simp only [adapterIsa, hissue]

/-- Selection: an unpermitted issue refuses. -/
theorem adapterIsa_gibAus_verweigert (m : HwMaschine) (c : Nat)
    (a : Adresse) (v : Byte)
    (hissue : issueByte (tsoAnsicht m) c a v = none) :
    adapterIsa.schritt m c (.gibAus a v) = none := by
  simp only [adapterIsa, hissue]

/-- Selection: the refusal event refuses. -/
theorem adapterIsa_verweigert (m : HwMaschine) (c : Nat) :
    adapterIsa.schritt m c .verweigert = none := rfl

/-! ## 3. Preservation and agreement with the accepted evaluator.

  Every adapter step preserves well-formedness, and a successful
  register step carries EXACTLY the `stepI` successor's register file,
  flags and RIP over the shared memory. -/

/-- Every adapter step preserves well-formedness. -/
theorem adapterIsa_wf (m m' : HwMaschine) (c : Nat) (e : IsaEreignis)
    (h : adapterIsa.schritt m c e = some m') (hwf : HwWf m) : HwWf m' := by
  cases e with
  | reg d =>
    cases hstep : stepI d (projZustand m c) with
    | some s' =>
      cases hg : isaNurRegister d.instr with
      | true =>
        have e := adapterIsa_reg m c d s' hstep hg
        rw [e] at h
        cases h
        exact setKernVonZustand_wf m c s' hwf
      | false =>
        have e := adapterIsa_reg_verweigert_speicher m c d s' hstep hg
        rw [e] at h
        cases h
    | none =>
      have e := adapterIsa_reg_verweigert_schritt m c d hstep
      rw [e] at h
      cases h
  | lade a v =>
    cases hload : loadByte (tsoAnsicht m) c a with
    | some w =>
      cases heq : (w == v) with
      | true =>
        have e := adapterIsa_lade m c a v w hload heq
        rw [e] at h
        cases h
        exact hwf
      | false =>
        have e := adapterIsa_lade_verweigert_wert m c a v w hload heq
        rw [e] at h
        cases h
    | none =>
      have e := adapterIsa_lade_verweigert m c a v hload
      rw [e] at h
      cases h
  | gibAus a v =>
    cases hissue : issueByte (tsoAnsicht m) c a v with
    | some s' =>
      have e := adapterIsa_gibAus m c a v s' hissue
      rw [e] at h
      cases h
      exact setTso_wf m s' hwf
    | none =>
      have e := adapterIsa_gibAus_verweigert m c a v hissue
      rw [e] at h
      cases h
  | verweigert =>
    have e := adapterIsa_verweigert m c
    rw [e] at h
    cases h

/-- Agreement with the accepted evaluator on the register projection:
    a successful adapter register step carries exactly the `stepI`
    successor's register file, flags and RIP over shared memory. -/
theorem adapterIsa_reg_stimmt (m : HwMaschine) (c : Nat)
    (d : InstrDecoded) (m' : HwMaschine)
    (h : adapterIsa.schritt m c (.reg d) = some m') :
    ∃ s' : Zustand, stepI d (projZustand m c) = some s' ∧
      (m'.kerne c).register = s'.register ∧
      (m'.kerne c).flags = s'.flags ∧ (m'.kerne c).rip = s'.rip ∧
      m'.mem = m.mem ∧ m'.puffer = m.puffer := by
  cases hstep : stepI d (projZustand m c) with
  | some s' =>
    cases hg : isaNurRegister d.instr with
    | true =>
      have e := adapterIsa_reg m c d s' hstep hg
      rw [e] at h
      cases h
      exact ⟨s', rfl, setKernVonZustand_register m c s',
        setKernVonZustand_flags m c s', setKernVonZustand_rip m c s',
        setKernVonZustand_speicher m c s',
        funext fun d => setKernVonZustand_puffer m c s' d⟩
    | false =>
      have e := adapterIsa_reg_verweigert_speicher m c d s' hstep hg
      rw [e] at h
      cases h
  | none =>
    have e := adapterIsa_reg_verweigert_schritt m c d hstep
    rw [e] at h
    cases h

/-- A store issue changes no canonical byte (buffer only): the
    adapter never substitutes an SC word effect, by the accepted
    `issue_kein_speicher`. -/
theorem adapterIsa_gibAus_kein_speicher (m m' : HwMaschine) (c : Nat)
    (a : Adresse) (v : Byte)
    (h : adapterIsa.schritt m c (.gibAus a v) = some m') (x : Adresse) :
    m'.mem.bytes x = m.mem.bytes x := by
  cases hissue : issueByte (tsoAnsicht m) c a v with
  | some s' =>
    have e := adapterIsa_gibAus m c a v s' hissue
    rw [e] at h
    cases h
    exact issue_kein_speicher (tsoAnsicht m) s' c a v hissue x
  | none =>
    have e := adapterIsa_gibAus_verweigert m c a v hissue
    rw [e] at h
    cases h

/-! ## 4. Agreement with the unified dispatcher on every shared form.

  `stepExt` covers pilot, narrow, mul/div, shift, SETcc and CMOVcc --
  six of the strand's seven families. On each of them the strand step
  and the dispatcher step coincide, by the accepted selection lemmas;
  the old evaluators are cited, never re-run. Compact and core forms
  have NO `ExtInstr` counterpart (see CUTS): that gap is reported, not
  papered over. -/

/-- Shared form `pilot`: `stepI` success IS unified `weiter`. -/
theorem isa_stepExt_pilot (b : Befehl) (l : Nat) (t : FpZustand)
    (bp : BereitProfil) (s' : Zustand)
    (h : stepI ⟨.pilot b, l⟩ t.kern = some s') :
    stepExt (.pilot ⟨b, l⟩) t bp = .weiter { t with kern := s' } := by
  have hl : laufAlt ⟨b, l⟩ t = some { t with kern := s' } := by
    unfold laufAlt
    rw [stepI_pilot] at h
    rw [h]
  exact stepExt_pilot ⟨b, l⟩ t _ bp hl

/-- Shared form `pilot`: `stepI` refusal IS unified refusal. -/
theorem isa_stepExt_pilot_verweigert (b : Befehl) (l : Nat)
    (t : FpZustand) (bp : BereitProfil)
    (h : stepI ⟨.pilot b, l⟩ t.kern = none) :
    stepExt (.pilot ⟨b, l⟩) t bp = .verweigert := by
  have hl : laufAlt ⟨b, l⟩ t = none := by
    unfold laufAlt
    rw [stepI_pilot] at h
    rw [h]
  exact stepExt_pilot_verweigert ⟨b, l⟩ t bp hl

/-- Shared form `narrow`: `stepI` success IS unified `weiter`. -/
theorem isa_stepExt_narrow (o : NarrowOp) (l : Nat) (t : FpZustand)
    (bp : BereitProfil) (s' : Zustand)
    (h : stepI ⟨.narrow o, l⟩ t.kern = some s') :
    stepExt (.narrow ⟨o, l⟩) t bp = .weiter { t with kern := s' } := by
  rw [stepI_narrow] at h
  exact stepExt_narrow ⟨o, l⟩ t bp s' h

/-- Shared form `narrow`: `stepI` refusal IS unified refusal. -/
theorem isa_stepExt_narrow_verweigert (o : NarrowOp) (l : Nat)
    (t : FpZustand) (bp : BereitProfil)
    (h : stepI ⟨.narrow o, l⟩ t.kern = none) :
    stepExt (.narrow ⟨o, l⟩) t bp = .verweigert := by
  rw [stepI_narrow] at h
  exact stepExt_narrow_verweigert ⟨o, l⟩ t bp h

/-- Shared form `muldiv`: `stepI` success IS unified `weiter`. -/
theorem isa_stepExt_muldiv_ok (b : MulDivBefehl) (l : Nat) (t : FpZustand)
    (bp : BereitProfil) (s' : Zustand)
    (h : stepI ⟨.muldiv b, l⟩ t.kern = some s') :
    stepExt (.muldiv ⟨b, l⟩) t bp = .weiter { t with kern := s' } := by
  rw [stepI_muldiv] at h
  cases hmul : mulDivSchritt ⟨b, l⟩ t.kern with
  | ok t' =>
    simp [hmul, MulDivErgebnis.nachfolger] at h
    subst h
    exact stepExt_muldiv_ok ⟨b, l⟩ t bp t' hmul
  | hardwareHalt =>
    simp [hmul, MulDivErgebnis.nachfolger] at h
  | misslungen =>
    simp [hmul, MulDivErgebnis.nachfolger] at h

/-- Shared form `muldiv`: the divide trap IS the unified halt. -/
theorem isa_stepExt_muldiv_halt (b : MulDivBefehl) (l : Nat)
    (t : FpZustand) (bp : BereitProfil)
    (h : stepIE ⟨.muldiv b, l⟩ t.kern = .hardwareHalt) :
    stepExt (.muldiv ⟨b, l⟩) t bp = .halt := by
  have hmul : mulDivSchritt ⟨b, l⟩ t.kern = .hardwareHalt := by
    simpa [stepIE] using h
  exact stepExt_muldiv_halt ⟨b, l⟩ t bp hmul

/-- Shared form `muldiv`: refusal IS unified refusal. -/
theorem isa_stepExt_muldiv_misslungen (b : MulDivBefehl) (l : Nat)
    (t : FpZustand) (bp : BereitProfil)
    (h : stepIE ⟨.muldiv b, l⟩ t.kern = .misslungen) :
    stepExt (.muldiv ⟨b, l⟩) t bp = .verweigert := by
  have hmul : mulDivSchritt ⟨b, l⟩ t.kern = .misslungen := by
    simpa [stepIE] using h
  exact stepExt_muldiv_misslungen ⟨b, l⟩ t bp hmul

/-- Shared form `muldiv`: `stepI` silence is exactly halt-or-refusal,
    never a hidden successor. -/
theorem isa_stepExt_muldiv_verweigert_oder_halt (b : MulDivBefehl)
    (l : Nat) (t : FpZustand) (bp : BereitProfil)
    (h : stepI ⟨.muldiv b, l⟩ t.kern = none) :
    stepExt (.muldiv ⟨b, l⟩) t bp = .verweigert ∨
      stepExt (.muldiv ⟨b, l⟩) t bp = .halt := by
  rw [stepI_muldiv] at h
  cases hmul : mulDivSchritt ⟨b, l⟩ t.kern with
  | ok t' =>
    simp [hmul, MulDivErgebnis.nachfolger] at h
  | hardwareHalt =>
    exact Or.inr (stepExt_muldiv_halt ⟨b, l⟩ t bp hmul)
  | misslungen =>
    exact Or.inl (stepExt_muldiv_misslungen ⟨b, l⟩ t bp hmul)

/-- Shared form `shift`: `stepI` success IS unified `weiter`. -/
theorem isa_stepExt_shift (f : ShiftForm) (l : Nat) (t : FpZustand)
    (bp : BereitProfil) (s' : Zustand)
    (h : stepI ⟨.shift f, l⟩ t.kern = some s') :
    stepExt (.shift ⟨f, l⟩) t bp = .weiter { t with kern := s' } := by
  rw [stepI_shift] at h
  exact stepExt_shift ⟨f, l⟩ t bp s' h

/-- Shared form `shift`: `stepI` refusal IS unified refusal. -/
theorem isa_stepExt_shift_verweigert (f : ShiftForm) (l : Nat)
    (t : FpZustand) (bp : BereitProfil)
    (h : stepI ⟨.shift f, l⟩ t.kern = none) :
    stepExt (.shift ⟨f, l⟩) t bp = .verweigert := by
  rw [stepI_shift] at h
  exact stepExt_shift_verweigert ⟨f, l⟩ t bp h

/-- Shared form `setcc`: `stepI` success IS unified `weiter`. -/
theorem isa_stepExt_setcc (c : Bedingung) (dst : Register) (l : Nat)
    (t : FpZustand) (bp : BereitProfil) (s' : Zustand)
    (h : stepI ⟨.cond (.setcc c dst), l⟩ t.kern = some s') :
    stepExt (.setcc c dst l) t bp = .weiter { t with kern := s' } := by
  rw [stepI_setcc] at h
  exact stepExt_setcc c dst l t bp s' h

/-- Shared form `setcc`: `stepI` refusal IS unified refusal. -/
theorem isa_stepExt_setcc_verweigert (c : Bedingung) (dst : Register)
    (l : Nat) (t : FpZustand) (bp : BereitProfil)
    (h : stepI ⟨.cond (.setcc c dst), l⟩ t.kern = none) :
    stepExt (.setcc c dst l) t bp = .verweigert := by
  rw [stepI_setcc] at h
  exact stepExt_setcc_verweigert c dst l t bp h

/-- Shared form `cmov`: `stepI` success IS unified `weiter`. -/
theorem isa_stepExt_cmov (c : Bedingung) (dst src : Register) (l : Nat)
    (t : FpZustand) (bp : BereitProfil) (s' : Zustand)
    (h : stepI ⟨.cond (.cmov c dst src), l⟩ t.kern = some s') :
    stepExt (.cmov c dst src l) t bp = .weiter { t with kern := s' } := by
  rw [stepI_cmov] at h
  exact stepExt_cmov c dst src l t bp s' h

/-- Shared form `cmov`: `stepI` refusal IS unified refusal. -/
theorem isa_stepExt_cmov_verweigert (c : Bedingung) (dst src : Register)
    (l : Nat) (t : FpZustand) (bp : BereitProfil)
    (h : stepI ⟨.cond (.cmov c dst src), l⟩ t.kern = none) :
    stepExt (.cmov c dst src l) t bp = .verweigert := by
  rw [stepI_cmov] at h
  exact stepExt_cmov_verweigert c dst src l t bp h

/-! ## 5. Planted refusals: what is NOT admitted is refused.

  The divide trap has no register successor, memory forms never take
  the register path (even where their SC step succeeds), and the byte
  events refuse without permission. Every refusal is explicit. -/

/-- Poison probe: a zero decoded length refuses on the register path,
    on every machine and core. -/
theorem adapterIsa_schlechte_laenge (m : HwMaschine) (c : Nat) :
    adapterIsa.schritt m c
      (.reg ⟨.core (.lea64 .rdx .rbx none 16), 0⟩) = none := by
  have hstep : stepI
      (⟨.core (.lea64 .rdx .rbx none 16), 0⟩ : InstrDecoded)
      (projZustand m c) = none := by
    simp [stepI, coreSchritt, laengeOk]
  exact adapterIsa_reg_verweigert_schritt m c _ hstep

/-- The divide trap is refused on the register path: a trap is an
    outcome, never a successor state. -/
theorem adapterIsa_falle_verweigert (m : HwMaschine) (c : Nat)
    (b : MulDivBefehl) (l : Nat)
    (h : mulDivSchritt ⟨b, l⟩ (projZustand m c) = .hardwareHalt) :
    adapterIsa.schritt m c (.reg ⟨.muldiv b, l⟩) = none := by
  have hstep : stepI (⟨.muldiv b, l⟩ : InstrDecoded)
      (projZustand m c) = none := by
    rw [stepI_muldiv, h]
    rfl
  exact adapterIsa_reg_verweigert_schritt m c _ hstep

/-- The trap refusal through the full outcome: `hardwareHalt` carries
    no successor for the register path. -/
theorem adapterIsa_falle_kein_nachfolger (m : HwMaschine) (c : Nat)
    (b : MulDivBefehl) (l : Nat)
    (h : stepIE ⟨.muldiv b, l⟩ (projZustand m c) = .hardwareHalt) :
    adapterIsa.schritt m c (.reg ⟨.muldiv b, l⟩) = none := by
  have hmul : mulDivSchritt ⟨b, l⟩ (projZustand m c) = .hardwareHalt := by
    simpa [stepIE] using h
  exact adapterIsa_falle_verweigert m c b l hmul

/-- A compact store is refused on the register path even where its SC
    step succeeds: stores travel buffered, never in place. -/
theorem adapterIsa_speicherform_verweigert (m : HwMaschine) (c : Nat)
    (base src : Register) (l : Nat) (s' : Zustand)
    (hstep : stepI (⟨.compact (.store64Disp0 base src), l⟩ : InstrDecoded)
      (projZustand m c) = some s') :
    adapterIsa.schritt m c
      (.reg ⟨.compact (.store64Disp0 base src), l⟩) = none := by
  have hg : isaNurRegister
      (Instr.compact (.store64Disp0 base src)) = false := rfl
  exact adapterIsa_reg_verweigert_speicher m c _ s' hstep hg

/-- A store issue without write permission refuses. -/
theorem adapterIsa_ausgabe_ohne_schreibrecht (m : HwMaschine) (c : Nat)
    (a : Adresse) (v : Byte)
    (h : (tsoAnsicht m).mem.schreibbar a = false) :
    adapterIsa.schritt m c (.gibAus a v) = none := by
  have hissue : issueByte (tsoAnsicht m) c a v = none :=
    issue_verweigert (tsoAnsicht m) c a v h
  exact adapterIsa_gibAus_verweigert m c a v hissue

/-- A load without read permission refuses. -/
theorem adapterIsa_laden_ohne_leserecht (m : HwMaschine) (c : Nat)
    (a : Adresse) (v : Byte)
    (h : (tsoAnsicht m).mem.lesbar a = false) :
    adapterIsa.schritt m c (.lade a v) = none := by
  have hload : loadByte (tsoAnsicht m) c a = none :=
    load_verweigert (tsoAnsicht m) c a h
  exact adapterIsa_lade_verweigert m c a v hload

/-! ## 6. Joint witness: two cores, family steps, buffered store.

  Core 0 runs one step per new family over the shared witness memory
  (compact immediate move, core LEA, conditional select), each through
  the adapter register path with canonical lengths; then core 0 issues
  a buffered byte that core 1 still observes as absent (forwarding to
  the owner only), core 1 issues its own byte elsewhere, and core 0
  drains into shared memory. The register path changes no memory and
  issues nothing; the drain changes actual shared memory. -/

/-- Witness cores: core 0 runs the family steps with `rbx` on the
    data cells; core 1 idles on the data page. -/
def isaFamKern : Nat → HwKern
  | 0 => ⟨isaReg, witnessFlags, BitVec.ofNat 64 4096,
      fun _ => BitVec.ofNat 128 0, kontextReset⟩
  | _ => ⟨fun _ => BitVec.ofNat 64 0, witnessFlags,
      BitVec.ofNat 64 8192, fun _ => BitVec.ofNat 128 0, kontextReset⟩

/-- Witness start machine: shared witness memory, two cores, empty
    buffers, full silicon. -/
def isaFamM0 : HwMaschine :=
  ⟨isaSpeicher, isaFamKern, fun _ => [], basisHw, fun _ => basisBereit⟩

/-- The witness machine is well-formed. -/
theorem isaFamM0_wf : HwWf isaFamM0 := by
  intro c f _
  cases f <;> rfl

/-- Step one: compact zero-extending immediate move into `rax`. -/
def isaFamM1 : Option HwMaschine :=
  adapterIsa.schritt isaFamM0 0
    (.reg (canonI (.compact (.movImm32Zx .rax 42))))

/-- Step two: core LEA of `rbx + 16` into `rdx`. -/
def isaFamM2 : Option HwMaschine :=
  match isaFamM1 with
  | some m => adapterIsa.schritt m 0
      (.reg (canonI (.core (.lea64 .rdx .rbx none 16))))
  | none => none

/-- Step three: conditional select from the witness flags. -/
def isaFamM3 : Option HwMaschine :=
  match isaFamM2 with
  | some m => adapterIsa.schritt m 0
      (.reg (canonI (.cond (.setcc .ne .rdx))))
  | none => none

/-- Read a core register out of an adapter outcome. -/
def isaFamRegOut (o : Option HwMaschine) (c : Nat)
    (q : Register) : Option Wort :=
  match o with
  | some m => some ((m.kerne c).register q)
  | none => none

/-- Read a core RIP out of an adapter outcome. -/
def isaFamRipOut (o : Option HwMaschine) (c : Nat) : Option Wort :=
  match o with
  | some m => some (m.kerne c).rip
  | none => none

/-- Read a shared-memory byte out of an adapter outcome. -/
def isaFamMemOut (o : Option HwMaschine) (a : Adresse) : Option Byte :=
  match o with
  | some m => some (m.mem.bytes a)
  | none => none

/-- Read a buffer length out of an adapter outcome. -/
def isaFamBufOut (o : Option HwMaschine) (c : Nat) : Option Nat :=
  match o with
  | some m => some (m.puffer c).length
  | none => none

/-- Witness data address. -/
def isaFamAdr : Adresse := BitVec.ofNat 64 8192

/-- Step one moves 42 into `rax`. -/
theorem isaFamM1_rax : isaFamRegOut isaFamM1 0 .rax = some 42 := by
  decide

/-- Step one advances RIP past the canonical compact move. -/
theorem isaFamM1_rip : isaFamRipOut isaFamM1 0 =
    some (ripNach (BitVec.ofNat 64 4096)
      (encodeI (.compact (.movImm32Zx .rax 42))).length) := by
  decide

/-- Step one leaves shared memory alone. -/
theorem isaFamM1_mem : isaFamMemOut isaFamM1 isaFamAdr =
    some (BitVec.ofNat 8 0) := by
  decide

/-- Step one issues no buffer entry. -/
theorem isaFamM1_puffer : isaFamBufOut isaFamM1 0 = some 0 := by
  decide

/-- Step two computes `rbx + 16 = 8208` into `rdx`. -/
theorem isaFamM2_rdx : isaFamRegOut isaFamM2 0 .rdx =
    some (BitVec.ofNat 64 8208) := by
  decide

/-- Step two advances RIP past the canonical LEA. -/
theorem isaFamM2_rip : isaFamRipOut isaFamM2 0 =
    some (ripNach (ripNach (BitVec.ofNat 64 4096)
      (encodeI (.compact (.movImm32Zx .rax 42))).length)
      (encodeI (.core (.lea64 .rdx .rbx none 16))).length) := by
  decide

/-- Steps one and two leave shared memory alone. -/
theorem isaFamM2_mem : isaFamMemOut isaFamM2 isaFamAdr =
    some (BitVec.ofNat 8 0) := by
  decide

/-- Steps one and two issue no buffer entry. -/
theorem isaFamM2_puffer : isaFamBufOut isaFamM2 0 = some 0 := by
  decide

/-- Step three sets the low byte of `rdx` (`zf` is clear): `8208`
    becomes `8193`, upper bytes preserved. -/
theorem isaFamM3_rdx : isaFamRegOut isaFamM3 0 .rdx =
    some (BitVec.ofNat 64 8193) := by
  decide

/-- Step three advances RIP past the 4-byte select. -/
theorem isaFamM3_rip : isaFamRipOut isaFamM3 0 =
    some (ripNach (ripNach (ripNach (BitVec.ofNat 64 4096)
      (encodeI (.compact (.movImm32Zx .rax 42))).length)
      (encodeI (.core (.lea64 .rdx .rbx none 16))).length) 4) := by
  decide

/-- All three register steps leave shared memory alone. -/
theorem isaFamM3_mem : isaFamMemOut isaFamM3 isaFamAdr =
    some (BitVec.ofNat 8 0) := by
  decide

/-- All three register steps issue no buffer entry. -/
theorem isaFamM3_puffer : isaFamBufOut isaFamM3 0 = some 0 := by
  decide

/-- Core 0 issues byte 42 at the data cell. -/
def isaFamTso1 : Option TSOZustand :=
  match isaFamM3 with
  | some m => issueByte (tsoAnsicht m) 0 isaFamAdr (BitVec.ofNat 8 42)
  | none => none

/-- Core 0 observes its own byte (forwarding). -/
def isaFamLoadEigen : Option (Option Byte) :=
  match isaFamTso1 with
  | some s => some (loadByte s 0 isaFamAdr)
  | none => none

/-- Core 1 observes the old byte (no foreign forwarding). -/
def isaFamLoadFremd : Option (Option Byte) :=
  match isaFamTso1 with
  | some s => some (loadByte s 1 isaFamAdr)
  | none => none

/-- Core 1 issues its own byte at the neighbouring cell. -/
def isaFamTso2 : Option TSOZustand :=
  match isaFamTso1 with
  | some s => issueByte s 1 (BitVec.ofNat 64 8200) (BitVec.ofNat 8 7)
  | none => none

/-- Core 0 drains its oldest entry into shared memory. -/
def isaFamTso3 : Option TSOZustand :=
  match isaFamTso2 with
  | some s => flushKern s 0
  | none => none

/-- The shared byte after the drain. -/
def isaFamNachFlush : Option (Option Byte) :=
  match isaFamTso3 with
  | some s => some (some (s.mem.bytes isaFamAdr))
  | none => none

/-- Forwarding: core 0 reads its own unflushed byte. -/
theorem isaFam_weiterleitung :
    isaFamLoadEigen = some (some (BitVec.ofNat 8 42)) := by
  decide

/-- No foreign forwarding: core 1 still reads zero. -/
theorem isaFam_fremd_alt :
    isaFamLoadFremd = some (some (BitVec.ofNat 8 0)) := by
  decide

/-- The drain changes shared memory: the cell reads 42. -/
theorem isaFam_spuelung_aendert_speicher :
    isaFamNachFlush = some (some (BitVec.ofNat 8 42)) := by
  decide

/-- Poison probe on the witness machine: the compact store is refused
    on the register path even though its SC step succeeds. -/
theorem isaFam_speicherform_verweigert :
    adapterIsa.schritt isaFamM0 0
      (.reg (canonI (.compact (.store64Disp0 .rbx .rax)))) = none := by
  rfl

/-- The joint witness: a reached two-core run that executes one step
    per new family through the adapter (compact move, core LEA,
    conditional select), refuses the compact store on the register
    path, forwards a buffered store to its owner only, and drains it
    into shared memory (0 becomes 42). Non-degenerate: the drain
    changes ACTUAL shared memory, and every register step changes
    core state. -/
theorem isaFam_zeuge :
    HwWf isaFamM0 ∧
    isaFamRegOut isaFamM1 0 .rax = some 42 ∧
    isaFamRegOut isaFamM2 0 .rdx = some (BitVec.ofNat 64 8208) ∧
    isaFamRegOut isaFamM3 0 .rdx = some (BitVec.ofNat 64 8193) ∧
    isaFamMemOut isaFamM3 isaFamAdr = some (BitVec.ofNat 8 0) ∧
    isaFamBufOut isaFamM3 0 = some 0 ∧
    adapterIsa.schritt isaFamM0 0
      (.reg (canonI (.compact (.store64Disp0 .rbx .rax)))) = none ∧
    isaFamLoadEigen = some (some (BitVec.ofNat 8 42)) ∧
    isaFamLoadFremd = some (some (BitVec.ofNat 8 0)) ∧
    isaFamNachFlush = some (some (BitVec.ofNat 8 42)) := by
  exact ⟨isaFamM0_wf, isaFamM1_rax, isaFamM2_rdx, isaFamM3_rdx,
    isaFamM3_mem, isaFamM3_puffer, isaFam_speicherform_verweigert,
    isaFam_weiterleitung, isaFam_fremd_alt,
    isaFam_spuelung_aendert_speicher⟩

/- CUTS:
    Proved here: the ISA strand (`Instr`/`stepI`) on the coherent
    machine -- a `HwAdapter` whose register path lifts the accepted
    `stepI` exactly for the classifier-admitted forms (frame proved
    per family, never redefined), whose memory events are exactly the
    accepted TSO byte equations (no SC word effect substituted), with
    exact agreement with `stepExt` on all six shared families
    (pilot, narrow, mul/div with the halt/refusal trichotomy, shift,
    setcc, cmov), planted refusals (bad length, divide trap, memory
    forms on the register path, missing permissions), and a reached
    two-core witness joining all of it with a memory-changing drain.
    NOT proved here, and not claimed:
    - No hardware correspondence: encodings are the accepted
      canonical subsets with self-consistency only, not x86 truth.
      Intel SDM headings checked for the claimed rows are listed in
      the file header; they are provenance, not proofs. In
      particular the LEA/shift/flag/sign-extension facts are the
      accepted Lean definitions, re-checked against the SDM text, not
      against silicon.
    - Compact and core forms have NO `ExtInstr`/`stepExt` counterpart:
      `decodeExt`/`stepExt` cover pilot, narrow, mul/div, shift,
      setcc, cmov, scalar FP and packed integer only. The byte-level
      decoder agreement (`decodeI` vs `decodeExt`) is OPEN, as is any
      fetched-byte (`Byteschritt`) connection for the new families.
    - No per-access target-to-W/GX simulation and no whole-word
      atomicity beyond the accepted byte-drain equations; the compact
      word store/load decomposition into eight ordered byte issues
      (with `WortGruppe`/`FremdFrei` discipline) is left to the
      word-grouping owners (lanes 666/720 territory), not redone here.
    - No LOCK RMW path (`Instr` has no lock vocabulary: refused by
      type), no interrupts, no faults beyond the carried divide halt,
      no timing/power behaviour.
    - This plug does NOT complete the hardware model; it fills the
      §11 producer slot for the ISA strand's compact/core/cond
      families only.
-/

#print axioms stepI_nurRegister_speicher
#print axioms adapterIsa_wf
#print axioms adapterIsa_reg_stimmt
#print axioms adapterIsa_gibAus_kein_speicher
#print axioms isa_stepExt_pilot
#print axioms isa_stepExt_narrow
#print axioms isa_stepExt_muldiv_ok
#print axioms isa_stepExt_muldiv_halt
#print axioms isa_stepExt_muldiv_misslungen
#print axioms isa_stepExt_muldiv_verweigert_oder_halt
#print axioms isa_stepExt_shift
#print axioms isa_stepExt_setcc
#print axioms isa_stepExt_cmov
#print axioms adapterIsa_schlechte_laenge
#print axioms adapterIsa_falle_verweigert
#print axioms adapterIsa_falle_kein_nachfolger
#print axioms adapterIsa_speicherform_verweigert
#print axioms adapterIsa_ausgabe_ohne_schreibrecht
#print axioms adapterIsa_laden_ohne_leserecht
#print axioms isaFamM0_wf
#print axioms isaFam_zeuge

end Gabbro.Grammatik.X86
