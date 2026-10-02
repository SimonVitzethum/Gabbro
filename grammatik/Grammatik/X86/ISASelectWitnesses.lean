/-
  File:      Grammatik/X86/ISASelectWitnesses.lean
  Subject:   Witnesses and poison probes for the decided selection pass
             `ISASelect.lean`.

  One straight-line program (pilot moves, an LEA-shaped mov/shl/add, an
  immediate add through a scratch register, two stores, a compare and a
  SETcc) is selected into a program that is 28 bytes shorter; BOTH programs
  are laid out in executable memory and run from actual bytes, and they
  reach the same data memory and the same registers outside the scratch
  list. The generic theorems are instantiated jointly on it. Poison probes:
  a flag reader after the LEA shape, live flags at the end, a jump, an
  undeclared scratch, a scratch read later, an immediate out of range, a
  read of a register that differs. Reuses the memory layout vocabulary of
  `ISAWitnesses.lean` (`isaSpeicher`, `isaStart`, `isaExec`, `isaDaten`).
-/
import Grammatik.X86.ISASelect
import Grammatik.X86.ISAWitnesses

namespace Gabbro.Grammatik.X86

/-! ## 1. The witness program and its selection. -/

/-- `rax := 6; rcx := 7; rdx := rcx; shl rdx, 2; add rdx, rax;
    r11 := 8; add rdx, r11; mov [rbx+8], rdx; mov [rbx], rax;
    cmp rax, rcx; setl r9b` -- written in the pilot long forms. -/
def selProg : List Instr :=
  [.pilot (.movImm64 .rax 6),
   .pilot (.movImm64 .rcx 7),
   .pilot (.movReg64 .rdx .rcx),
   .shift (.imm .shl .rdx 2),
   .pilot (.addReg64 .rdx .rax),
   .pilot (.movImm64 .r11 8),
   .pilot (.addReg64 .rdx .r11),
   .pilot (.store64 .rbx .rdx 8),
   .pilot (.store64 .rbx .rax 0),
   .pilot (.cmpReg64 .rax .rcx),
   .cond (.setcc .l .r9)]

/-- Declared scratch: only `r11`. Flags live at the end. -/
def selScratch : List Register := [.r11]

/-- The selected program, as the selector computes it. -/
def selErgebnis : List Instr :=
  [.compact (.movImm32Zx .rax 6),
   .compact (.movImm32Zx .rcx 7),
   .core (.lea64 .rdx .rax (some (.rcx, .s4)) 0),
   .compact (.aluImm8 .add .rdx 8),
   .compact (.store64Disp8 .rbx .rdx 8),
   .compact (.store64Disp0 .rbx .rax),
   .pilot (.cmpReg64 .rax .rcx),
   .cond (.setcc .l .r9)]

/-- The decided selector produces exactly `selErgebnis`. -/
theorem sel_wert : waehle selScratch true selProg = some selErgebnis := by
  decide

/-- 64 bytes become 36. -/
theorem sel_laengen :
    (progBytes selProg).length = 64 ∧ (progBytes selErgebnis).length = 36 := by
  decide

/-! ## 2. Both programs from actual bytes. -/

def selSpeicherAlt : Speicher :=
  { isaSpeicher with bytes := bytesAusProg (progBytes selProg) 4096 }

def selSpeicherNeu : Speicher :=
  { isaSpeicher with bytes := bytesAusProg (progBytes selErgebnis) 4096 }

def selStartAlt : Zustand := { isaStart with speicher := selSpeicherAlt }

def selStartNeu : Zustand := { isaStart with speicher := selSpeicherNeu }

/-- Observation: rax, rdx, r9, the data bytes at 8192 and 8200. (RIP and
    the scratch `r11` are deliberately not observed.) -/
def selBeob (s : Zustand) : Wort × Wort × Wort × Byte × Byte :=
  (s.register .rax, s.register .rdx, s.register .r9,
    s.speicher.bytes (BitVec.ofNat 64 8192), s.speicher.bytes (BitVec.ofNat 64 8200))

def selAusgang : ByteAusgang → Option (Wort × Wort × Wort × Byte × Byte)
  | .weiter s => some (selBeob s)
  | .verweigert => none

/-- The ORIGINAL long program, 11 byte steps from actual memory:
    rdx = 6 + 7*4 + 8 = 42 stored at 8200, rax = 6 stored at 8192,
    6 < 7 sets r9 to 1; RIP ends 64 bytes past the start. -/
theorem sel_alt_bytes :
    selAusgang (laufBytesI 11 selStartAlt) = some (6, 42, 1, 6, 42) ∧
      ausgangRip (laufBytesI 11 selStartAlt) = some (BitVec.ofNat 64 (4096 + 64)) := by
  decide

/-- The SELECTED short program, 8 byte steps from actual memory: the same
    observation; RIP ends 36 bytes past the start. -/
theorem sel_neu_bytes :
    selAusgang (laufBytesI 8 selStartNeu) = some (6, 42, 1, 6, 42) ∧
      ausgangRip (laufBytesI 8 selStartNeu) = some (BitVec.ofNat 64 (4096 + 36)) := by
  decide

/-- The scratch register is where the two runs differ: the original
    loaded 8 into r11, the selected program never touched it. -/
theorem sel_scratch_unterschied :
    (laufI (selProg.map canonI) isaStart).map (fun s => s.register .r11) = some 8 ∧
      (laufI (selErgebnis.map canonI) isaStart).map (fun s => s.register .r11) = some 0 := by
  decide

theorem selSpeicherNeu_wx : WX selStartNeu.speicher := by
  intro x hx
  simp only [selStartNeu, selSpeicherNeu, isaSpeicher, isaExec, decide_eq_true_eq] at hx
  show isaDaten x = false
  simp only [isaDaten, decide_eq_false_iff_not]
  omega

theorem selStartNeu_code :
    CodeAt selStartNeu.speicher selStartNeu.rip (progBytes selErgebnis) := by
  intro i hi
  have hl : i < 36 := by rw [sel_laengen.2] at hi; exact hi
  revert i
  decide

/-- JOINT WITNESS for `waehle_korrekt`, `waehle_lauf` and `waehle_bytes`:
    the selector accepts the program and returns a DIFFERENT, 28 bytes
    shorter program; from the witness state both runs succeed, change two
    zeroed data bytes and agree outside the scratch list (observed: rax,
    rdx, r9, both data bytes); the selected program's byte run from actual
    memory is its `laufI` run. -/
theorem waehle_zeuge :
    ∃ (S : List Register) (fe : Bool) (p q : List Instr) (s : Zustand),
      waehle S fe p = some q ∧ q ≠ p ∧
      (progBytes q).length + 28 = (progBytes p).length ∧
      OptRel (EndGl S fe) (laufI (p.map canonI) s) (laufI (q.map canonI) s) ∧
      (laufI (p.map canonI) s).map selBeob = some (6, 42, 1, 6, 42) ∧
      (laufI (q.map canonI) s).map selBeob = some (6, 42, 1, 6, 42) ∧
      s.speicher.bytes (BitVec.ofNat 64 8200) = 0 ∧
      WX selStartNeu.speicher ∧
      laufBytesI q.length selStartNeu = ausgangVon (laufI (q.map canonI) selStartNeu) := by
  refine ⟨selScratch, true, selProg, selErgebnis, isaStart, sel_wert, by decide,
    by decide, waehle_korrekt _ _ _ _ sel_wert _, by decide, by decide, by decide,
    selSpeicherNeu_wx, waehle_bytes _ _ _ _ sel_wert _ selSpeicherNeu_wx selStartNeu_code⟩

/-- Witness for `waehle_lauf`: the complete statement on the program. -/
theorem waehle_lauf_zeuge :
    (∀ i ∈ selErgebnis, kanonischI i = true ∧ faelltDurchI i = true) ∧
      (progBytes selErgebnis).length ≤ (progBytes selProg).length ∧
      ((laufI (selProg.map canonI) isaStart = none ∧
          laufI (selErgebnis.map canonI) isaStart = none) ∨
        ∃ s1 s2, laufI (selProg.map canonI) isaStart = some s1 ∧
          laufI (selErgebnis.map canonI) isaStart = some s2 ∧
          EndGl selScratch true s1 s2 ∧
          s1.rip = ripNach isaStart.rip (progBytes selProg).length ∧
          s2.rip = ripNach isaStart.rip (progBytes selErgebnis).length) :=
  waehle_lauf _ _ _ _ sel_wert isaStart

/-- Witness for `wahl_korrekt` with a NON-EMPTY difference set and
    differing start states: r11 already differs and the flags already
    differ; the selected suffix still agrees outside the scratch. -/
theorem wahl_korrekt_zeuge :
    OptRel (EndGl selScratch true)
      (laufI ((selProg.drop 5).map canonI)
        { isaStart with register := fun q => if q = .r11 then 99 else isaStart.register q })
      (laufI ((selErgebnis.drop 3).map canonI) isaStart) := by
  have hw : Wahl selScratch true [.r11] false (selProg.drop 5) (selErgebnis.drop 3) :=
    sel_wahl _ _ _ _ _ _ (by decide)
  apply wahl_korrekt _ _ _ _ _ _ hw
  · intro r hr; simpa [selScratch] using hr
  · refine ⟨fun r hr => ?_, rfl, fun h => by cases h⟩
    have : r ≠ .r11 := by simpa using hr
    show (if r = .r11 then 99 else isaStart.register r) = isaStart.register r
    rw [if_neg this]

/-! ## 3. Poison probes: where the selector refuses or keeps the long form. -/

/-- The LEA shape without a later flag reader. -/
def leaForm : List Instr :=
  [.pilot (.movReg64 .rdx .rcx), .shift (.imm .shl .rdx 2), .pilot (.addReg64 .rdx .rax)]

/-- Flags DEAD at the end: the LEA is selected (10 bytes become 8). -/
theorem lea_tot_gewaehlt :
    waehle [] false leaForm = some [.core (.lea64 .rdx .rax (some (.rcx, .s4)) 0)] := by
  decide

/-- POISON (flags live at the end): the LEA would drop the ADD's flags, so
    the selector keeps the long form. -/
theorem gift_flags_lebend_ende : waehle [] true leaForm = some leaForm := by
  decide

/-- POISON (flag reader): a SETcc right after the LEA shape reads the ADD's
    flags; the LEA is refused even with dead flags at the end. -/
theorem gift_flags_gelesen :
    waehle [] false (leaForm ++ [.cond (.setcc .e .r9)]) =
      some (leaForm ++ [.cond (.setcc .e .r9)]) := by
  decide

/-- A fresh flag writer between the LEA and the reader makes the flags dead
    again: the LEA is selected. -/
theorem flags_neu_geschrieben :
    waehle [] true (leaForm ++ [.pilot (.cmpReg64 .rax .rcx), .cond (.setcc .e .r9)]) =
      some [.core (.lea64 .rdx .rax (some (.rcx, .s4)) 0), .pilot (.cmpReg64 .rax .rcx),
        .cond (.setcc .e .r9)] := by
  decide

/-- POISON (control flow): a program with a jump is refused outright --
    a shorter encoding before the target would move it, and no layout
    revalidation is done here. The same holds for a compact rel8 jump and
    for a call. -/
theorem gift_sprung :
    waehle [] false [.pilot (.movImm64 .rax 6), .pilot (.jump32 0)] = none ∧
      waehle [] false [.pilot (.jumpIf32 .e 0), .pilot (.movImm64 .rax 6)] = none ∧
      waehle [] false [.compact (.jump8 0)] = none ∧
      waehle [] false [.pilot (.call32 0)] = none := by
  decide

/-- The ALU-immediate shape. -/
def aluForm : List Instr := [.pilot (.movImm64 .r11 8), .pilot (.addReg64 .rdx .r11)]

/-- With `r11` declared scratch the immediate form is selected. -/
theorem alu_gewaehlt :
    waehle [.r11] true aluForm = some [.compact (.aluImm8 .add .rdx 8)] := by
  decide

/-- POISON (undeclared scratch): without `r11` in the scratch list the
    immediate rewrite would change a live register; only the MOV is
    compacted. -/
theorem gift_kein_scratch :
    waehle [] true aluForm =
      some [.compact (.movImm32Zx .r11 8), .pilot (.addReg64 .rdx .r11)] := by
  decide

/-- POISON (scratch read later): a later read of `r11` sees a register
    that differs after the immediate rewrite; the rewrite is abandoned. -/
theorem gift_scratch_gelesen :
    waehle [.r11] true (aluForm ++ [.pilot (.movReg64 .rax .r11)]) =
      some [.compact (.movImm32Zx .r11 8), .pilot (.addReg64 .rdx .r11),
        .pilot (.movReg64 .rax .r11)] := by
  decide

/-- POISON (immediate out of range): `2^40` has no signed 32-bit
    immediate; the ALU rewrite and the MOV compaction are both refused. -/
theorem gift_imm_bereich :
    waehle [.r11] true [.pilot (.movImm64 .r11 (BitVec.ofNat 64 (2 ^ 40))),
        .pilot (.addReg64 .rdx .r11)] =
      some [.pilot (.movImm64 .r11 (BitVec.ofNat 64 (2 ^ 40))),
        .pilot (.addReg64 .rdx .r11)] := by
  decide

/-- POISON (LEA index `rsp`): an LEA cannot take `rsp` as index; the
    shape `mov d, rsp; shl d, 2; add d, a` keeps its long form. -/
theorem gift_lea_rsp :
    waehle [] false [.pilot (.movReg64 .rdx .rsp), .shift (.imm .shl .rdx 2),
        .pilot (.addReg64 .rdx .rax)] =
      some [.pilot (.movReg64 .rdx .rsp), .shift (.imm .shl .rdx 2),
        .pilot (.addReg64 .rdx .rax)] := by
  decide

/-- POISON (unsupported row): a family the selector has no frame lemma
    for (here a stack push) makes the whole selection refuse. -/
theorem gift_unbekannte_zeile :
    waehle [] false [.pilot (.movImm64 .rax 6), .pilot (.push64 .rax)] = none := by
  decide

/- CUTS (what is NOT proved here):
   - The witnesses are concrete selections and runs checked by kernel
     evaluation; they add no generic claim beyond `ISASelect.lean`.
   - The two byte runs start from DIFFERENT memories (each program at its
     own code bytes at 4096); they are compared by observation, not by the
     generic theorem, which compares `laufI` runs from one state.
-/

#print axioms sel_wert
#print axioms sel_laengen
#print axioms sel_alt_bytes
#print axioms sel_neu_bytes
#print axioms sel_scratch_unterschied
#print axioms selSpeicherNeu_wx
#print axioms selStartNeu_code
#print axioms waehle_zeuge
#print axioms waehle_lauf_zeuge
#print axioms wahl_korrekt_zeuge
#print axioms lea_tot_gewaehlt
#print axioms gift_flags_lebend_ende
#print axioms gift_flags_gelesen
#print axioms flags_neu_geschrieben
#print axioms gift_sprung
#print axioms alu_gewaehlt
#print axioms gift_kein_scratch
#print axioms gift_scratch_gelesen
#print axioms gift_imm_bereich
#print axioms gift_lea_rsp
#print axioms gift_unbekannte_zeile

end Gabbro.Grammatik.X86
