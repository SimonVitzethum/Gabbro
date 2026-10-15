/-
  File:      Grammatik/X86/ISARelaxWitnesses.lean
  Subject:   Witnesses and poison probes for branch relaxation and
             cross-block selection (`ISARelax.lean`).

  One block program with a LOOP (counter to 5 with a backward conditional
  jump, then a store) is selected per block (MOVs compacted, a scratch
  immediate folded into `add rax, 1`), flattened, relaxed (the backward
  `jl` becomes rel8) and laid out in executable memory; its byte run from
  actual memory stores 5 exactly as the ORIGINAL long block program does,
  and the generic theorems are instantiated jointly on it. A forward
  jump over 130 bytes stays rel32 (and runs), the same jump over 120 bytes
  is narrowed. Poison probes: a forged rel8 displacement, a label outside
  the program, a stale displacement left behind by a compression of
  another branch, a forged width vector, a raw jump as an ordinary row.
  Reuses the memory vocabulary of `ISAWitnesses.lean` (`isaSpeicher`,
  `isaStart`, `isaDaten`, `isaExec`) and `bytesAusProg`/`ausgangRip`
  (`Byteschritt.lean`).
-/
import Grammatik.X86.ISARelax
import Grammatik.X86.ISASelectWitnesses

namespace Gabbro.Grammatik.X86

/-! ## 1. The loop: select, flatten, relax. -/

/-- Block 0: `rax := 0; rcx := 5`. Block 1 (the loop): `r11 := 1;
    add rax, r11; cmp rax, rcx; jl block 1`. Block 2: `mov [rbx], rax`. -/
def loopProg : BProg :=
  [⟨[.pilot (.movImm64 .rax 0), .pilot (.movImm64 .rcx 5)], .weiter⟩,
   ⟨[.pilot (.movImm64 .r11 1), .pilot (.addReg64 .rax .r11), .pilot (.cmpReg64 .rax .rcx)],
     .jcc .l 1⟩,
   ⟨[.pilot (.store64 .rbx .rax 0)], .weiter⟩]

/-- Declared scratch: `r11`. -/
def loopS : List Register := [.r11]

/-- The selected block program (labels and terminators unchanged). -/
def loopQ : BProg :=
  [⟨[.compact (.movImm32Zx .rax 0), .compact (.movImm32Zx .rcx 5)], .weiter⟩,
   ⟨[.compact (.aluImm8 .add .rax 1), .pilot (.cmpReg64 .rax .rcx)], .jcc .l 1⟩,
   ⟨[.compact (.store64Disp0 .rbx .rax)], .weiter⟩]

/-- The relaxed widths of the flattening: only the backward `jl` (index 4)
    is narrowed. -/
def loopWs : List Bool := [false, false, false, false, true, false]

def loopBild : List Byte := bild loopWs (flach loopQ)

theorem loop_waehle : waehleB loopS loopProg = some loopQ := by decide

theorem loop_flach :
    flach loopQ =
      [.op (.compact (.movImm32Zx .rax 0)), .op (.compact (.movImm32Zx .rcx 5)),
       .op (.compact (.aluImm8 .add .rax 1)), .op (.pilot (.cmpReg64 .rax .rcx)),
       .jcc .l 2, .op (.compact (.store64Disp0 .rbx .rax))] := by decide

/-- RELAXATION: three rounds narrow the backward `jl` to rel8; with no
    fuel the validated all-wide layout is kept. 26 bytes become 22. -/
theorem loop_relax :
    relax 3 (flach loopQ) = some loopWs ∧
      relax 0 (flach loopQ) = some (alleWeit (flach loopQ)) ∧
      loopWs ≠ alleWeit (flach loopQ) ∧
      (bild (alleWeit (flach loopQ)) (flach loopQ)).length = 26 ∧
      loopBild.length = 22 := by
  decide

/-- The resolved short jump: `jl -9` (0x7C 0xF7) at offset 17, back to the
    loop head at offset 10. -/
theorem loop_sprung :
    aufgeloest loopWs (flach loopQ) =
      [.compact (.movImm32Zx .rax 0), .compact (.movImm32Zx .rcx 5),
       .compact (.aluImm8 .add .rax 1), .pilot (.cmpReg64 .rax .rcx),
       .compact (.jumpIf8 .l (BitVec.ofNat 8 0xF7)), .compact (.store64Disp0 .rbx .rax)] ∧
      off loopWs (flach loopQ) 2 = 10 ∧ off loopWs (flach loopQ) 4 = 17 := by
  decide

theorem loop_uebersetze : uebersetze loopS 3 loopProg = some (loopQ, loopWs, loopBild) := by
  decide

/-! ## 2. Runs: the original block program and the relaxed bytes. -/

def loopSpeicher (img : List Byte) : Speicher := { isaSpeicher with bytes := bytesAusProg img 4096 }

def loopStartVon (img : List Byte) : Zustand := { isaStart with speicher := loopSpeicher img }

def loopStart : Zustand := loopStartVon loopBild

/-- Observation: rax, rcx, the data byte at 8192. -/
def loopBeob (s : Zustand) : Wort × Wort × Byte :=
  (s.register .rax, s.register .rcx, s.speicher.bytes (BitVec.ofNat 64 8192))

def loopAusgang : ByteAusgang → Option (Wort × Wort × Byte × Adresse)
  | .weiter s => some (s.register .rax, s.register .rcx,
      s.speicher.bytes (BitVec.ofNat 64 8192), s.rip)
  | .verweigert => none

/-- The ORIGINAL long block program, 7 blocks (entry, 5 loop iterations,
    store), under ANY address map: it ends at the program end (label 3)
    with rax = 5 stored at 8192. -/
theorem loop_quelle :
    (laufB (fun _ => 0) loopProg 7 (0, isaStart)).map (fun y => (y.1, loopBeob y.2)) =
      some (3, 5, 5, 5) := by
  decide

/-- The RELAXED SELECTED image, 18 byte steps from actual memory (2 + 5*3
    + 1): the same observation; RIP ends 22 bytes past the start. -/
theorem loop_bytes :
    loopAusgang (laufBytesI 18 loopStart) = some (5, 5, 5, BitVec.ofNat 64 (4096 + 22)) := by
  decide

/-- Start memory: the data byte is still 0 (the run changes memory). -/
theorem loop_vorher : loopStart.speicher.bytes (BitVec.ofNat 64 8192) = 0 := by decide

theorem loop_wx (img : List Byte) : WX (loopStartVon img).speicher := by
  intro x hx
  simp only [loopStartVon, loopSpeicher, isaSpeicher, isaExec, decide_eq_true_eq] at hx
  show isaDaten x = false
  simp only [isaDaten, decide_eq_false_iff_not]
  omega

theorem loop_code : CodeAt loopStart.speicher loopStart.rip loopBild := by
  intro i hi
  have hl : i < 22 := by rw [loop_relax.2.2.2.2] at hi; exact hi
  revert i
  decide

/-- The labelled run of the flattening reaches the program end (label 6)
    after 18 steps, with the same observation. -/
theorem loop_flach_lauf :
    (laufL (adrL loopStart.rip loopWs (flach loopQ)) (flach loopQ) 18 (0, loopStart)).map
        (fun y => (y.1, loopBeob y.2)) = some (6, 5, 5, 5) ∧
      schritteL (adrL loopStart.rip loopWs (flach loopQ)) (flach loopQ) 18 (0, loopStart) = 18 := by
  decide

/-! ## 3. Joint witnesses of the generic theorems. -/

/-- JOINT WITNESS for `relax_laufBytes` / `laufBytesL_start` /
    `laufBytesL`: a loop with a backward rel8 jump, relaxed, in W^X
    memory; the byte run equals the labelled run, and both store 5. -/
theorem relax_laufBytes_zeuge :
    relax 3 (flach loopQ) = some loopWs ∧
      laufBytesI (schritteL (adrL loopStart.rip loopWs (flach loopQ)) (flach loopQ) 18
          (0, loopStart)) loopStart =
        ausgangVon ((laufL (adrL loopStart.rip loopWs (flach loopQ)) (flach loopQ) 18
          (0, loopStart)).map Prod.snd) ∧
      loopAusgang (laufBytesI 18 loopStart) = some (5, 5, 5, BitVec.ofNat 64 (4096 + 22)) ∧
      loopStart.speicher.bytes (BitVec.ofNat 64 8192) = 0 :=
  ⟨loop_relax.1,
    (relax_laufBytes 3 _ _ loop_relax.1 loopStart (loop_wx _) loop_code 18).1,
    loop_bytes, loop_vorher⟩

/-- JOINT WITNESS for `spurAn_layoutL`: the trace premise of
    `laufBytesI_spur`, DERIVED for the loop, and the trace theorem applied
    to it. -/
theorem spurAn_layoutL_zeuge :
    SpurAn (spurL loopWs (adrL loopStart.rip loopWs (flach loopQ)) (flach loopQ) 18
        (0, loopStart)) loopStart ∧
      (spurL loopWs (adrL loopStart.rip loopWs (flach loopQ)) (flach loopQ) 18
        (0, loopStart)).length = 18 ∧
      laufBytesI 18 loopStart =
        ausgangVon (laufI ((spurL loopWs (adrL loopStart.rip loopWs (flach loopQ))
          (flach loopQ) 18 (0, loopStart)).map canonI) loopStart) := by
  have hs := spurAn_layoutL loopStart.rip loopWs (flach loopQ) (relax_ok 3 _ _ loop_relax.1) 18
    (0, loopStart) ⟨by simp [adrL, off_null, ripNach_null], loop_wx _, loop_code⟩
  have hl : (spurL loopWs (adrL loopStart.rip loopWs (flach loopQ)) (flach loopQ) 18
      (0, loopStart)).length = 18 := by decide
  refine ⟨hs, hl, ?_⟩
  have := laufBytesI_spur _ loopStart hs
  rw [hl] at this
  exact this

/-- Scratch differs at the start: `r11 = 99` on the selected side. -/
def loopStartR11 : Zustand :=
  { isaStart with register := fun r => if r = .r11 then 99 else isaStart.register r }

/-- JOINT WITNESS for `waehleB_korrekt` and `waehleB_labels`: the selector
    accepts the loop with a DIFFERENT program and the same terminators;
    from start states that differ in the scratch register, the original
    and the selected block runs agree (same label, data byte 5). -/
theorem waehleB_korrekt_zeuge :
    loopQ ≠ loopProg ∧ loopQ.map Block.term = loopProg.map Block.term ∧
      OptRelP (GlB loopS) (laufB (fun _ => 0) loopProg 7 (0, isaStart))
        (laufB (fun b => BitVec.ofNat 64 (1000 + b)) loopQ 7 (0, loopStartR11)) ∧
      (laufB (fun b => BitVec.ofNat 64 (1000 + b)) loopQ 7 (0, loopStartR11)).map
        (fun y => (y.1, loopBeob y.2)) = some (3, 5, 5, 5) := by
  refine ⟨by decide, waehleB_labels _ _ _ loop_waehle,
    waehleB_korrekt _ _ _ loop_waehle _ _ 7 _ _ ⟨rfl, fun r hr => ?_, rfl, fun _ => rfl⟩,
    by decide⟩
  have : r ≠ .r11 := by simpa [loopS] using hr
  show isaStart.register r = (if r = .r11 then 99 else isaStart.register r)
  rw [if_neg this]

/-- JOINT WITNESS for `uebersetze_bytes`: the whole pass on the loop; the
    original long block program and the relaxed selected bytes, from one
    state, agree outside the scratch at the same block label, and the run
    changes memory (0 before, 5 after). -/
theorem uebersetze_bytes_zeuge :
    uebersetze loopS 3 loopProg = some (loopQ, loopWs, loopBild) ∧
      (∃ k : Nat,
        (laufB (fun _ => 0) loopProg 7 (0, loopStart) = none ∧
            laufBytesI k loopStart = .verweigert) ∨
        ∃ (b : Nat) (s1 s2 : Zustand), laufB (fun _ => 0) loopProg 7 (0, loopStart) = some (b, s1) ∧
          laufBytesI k loopStart = .weiter s2 ∧ EndGl loopS true s1 s2 ∧
          s2.rip = adrL loopStart.rip loopWs (flach loopQ) (startB loopQ b)) ∧
      (laufB (fun _ => 0) loopProg 7 (0, loopStart)).map (fun y => (y.1, loopBeob y.2)) =
        some (3, 5, 5, 5) ∧
      loopStart.speicher.bytes (BitVec.ofNat 64 8192) = 0 :=
  ⟨loop_uebersetze,
    uebersetze_bytes _ _ _ _ _ _ loop_uebersetze loopStart (loop_wx _) loop_code _ 7,
    by decide, loop_vorher⟩

/-! ## 4. A far branch stays rel32; a near one is narrowed. -/

/-- `jmp L; 13 × (rax := 7); L: rcx := 9` -- the target is 130 bytes past
    the jump's end. -/
def fernProg : LProg :=
  .jmp 14 :: (List.replicate 13 (.op (.pilot (.movImm64 .rax 7))) ++
    [.op (.pilot (.movImm64 .rcx 9))])

/-- The same with 12 moves: 120 bytes, within rel8. -/
def nahProg : LProg :=
  .jmp 13 :: (List.replicate 12 (.op (.pilot (.movImm64 .rax 7))) ++
    [.op (.pilot (.movImm64 .rcx 9))])

/-- FAR: the jump stays rel32 (130 > 127). NEAR: it is narrowed. -/
theorem fern_bleibt_weit :
    relax 3 fernProg = some (alleWeit fernProg) ∧
      relax 3 nahProg = some (true :: List.replicate 13 false) := by
  decide

def fernSpeicher : Speicher :=
  { isaSpeicher with
    bytes := bytesAusProg (bild (alleWeit fernProg) fernProg) 4096
    ausfuehrbar := fun a => decide (4096 ≤ a.toNat ∧ a.toNat < 4400) }

def fernStart : Zustand := { isaStart with speicher := fernSpeicher }

/-- The rel32 jump over 130 bytes runs: two byte steps skip every
    `rax := 7` and execute `rcx := 9` (rax stays 0); RIP ends past the
    145-byte image. -/
theorem fern_lauf :
    (laufBytesI 2 fernStart) matches .weiter _ ∧
      ausgangReg .rcx (laufBytesI 2 fernStart) = some 9 ∧
      ausgangReg .rax (laufBytesI 2 fernStart) = some 0 ∧
      ausgangRip (laufBytesI 2 fernStart) = some (BitVec.ofNat 64 (4096 + 145)) := by
  decide

theorem fern_wx : WX fernStart.speicher := by
  intro x hx
  simp only [fernStart, fernSpeicher, decide_eq_true_eq] at hx
  show isaDaten x = false
  simp only [isaDaten, decide_eq_false_iff_not]
  omega

set_option maxRecDepth 20000 in
theorem fern_code : CodeAt fernStart.speicher fernStart.rip (bild (alleWeit fernProg) fernProg) := by
  intro i hi
  have hl : i < 145 := by
    have : (bild (alleWeit fernProg) fernProg).length = 145 := by decide
    rw [this] at hi; exact hi
  revert i
  decide

/-- Witness of `laufBytesL_start` on the far branch (rel32 kept). -/
theorem fern_zeuge :
    laufBytesI (schritteL (adrL fernStart.rip (alleWeit fernProg) fernProg) fernProg 2
        (0, fernStart)) fernStart =
      ausgangVon ((laufL (adrL fernStart.rip (alleWeit fernProg) fernProg) fernProg 2
        (0, fernStart)).map Prod.snd) ∧
      (laufL (adrL fernStart.rip (alleWeit fernProg) fernProg) fernProg 2 (0, fernStart)).map
        Prod.fst = some 15 :=
  ⟨(relax_laufBytes 3 _ _ fern_bleibt_weit.1 fernStart fern_wx fern_code 2).1, by decide⟩

/-! ## 5. Poison probes. -/

/-- POISON (forged displacement): the `jl` byte forged from -9 to -11. The
    image check refuses it, and the forged byte run lands two bytes BEFORE
    the loop head -- inside the second `mov` -- after five steps, where the
    genuine image is at the loop head. -/
def loopGefaelscht : List Byte := loopBild.set 18 (BitVec.ofNat 8 0xF5)

theorem gift_verschiebung :
    bildOk loopWs (flach loopQ) loopBild = true ∧
      bildOk loopWs (flach loopQ) loopGefaelscht = false ∧
      ausgangRip (laufBytesI 5 loopStart) = some (BitVec.ofNat 64 (4096 + 10)) ∧
      ausgangRip (laufBytesI 5 (loopStartVon loopGefaelscht)) =
        some (BitVec.ofNat 64 (4096 + 8)) := by
  decide

/-- POISON (label outside the program): refused by the relaxation and by
    the whole pass. -/
theorem gift_label_aussen :
    relax 3 [.jmp 5, .op (.pilot (.movImm64 .rax 1))] = none ∧
      layoutOk [false, false] [.jmp 5, .op (.pilot (.movImm64 .rax 1))] = false ∧
      uebersetze loopS 3 [⟨[.pilot (.movImm64 .rax 1)], .jmp 9⟩] = none := by
  decide

/-- `jmp L; je L; rax := 1; L: rcx := 2`. Narrowing the `je` moves `L`
    four bytes earlier. -/
def staleProg : LProg :=
  [.jmp 3, .jcc .e 3, .op (.pilot (.movImm64 .rax 1)), .op (.pilot (.movImm64 .rcx 2))]

/-- Only the `je` narrowed. -/
def staleWs : List Bool := [false, true, false, false]

/-- POISON (a compression invalidates ANOTHER branch's bytes): the `je` is
    narrowed, but the `jmp` keeps the displacement computed in the all-wide
    layout. -/
def staleBild : List Byte :=
  progBytes [aufloesen (alleWeit staleProg) staleProg 0 (.jmp 3),
    aufloesenAt staleWs staleProg 1, aufloesenAt staleWs staleProg 2,
    aufloesenAt staleWs staleProg 3]

/-- The narrowed layout itself validates and its genuine image is accepted;
    the stale image is refused, and its `jmp` lands at offset 21 -- inside
    `rcx := 2`, which starts at 17 -- instead of at the label. -/
theorem gift_veraltet :
    layoutOk staleWs staleProg = true ∧
      bildOk staleWs staleProg (bild staleWs staleProg) = true ∧
      bildOk staleWs staleProg staleBild = false ∧
      adrL (BitVec.ofNat 64 4096) staleWs staleProg 3 = BitVec.ofNat 64 (4096 + 17) ∧
      ausgangRip (laufBytesI 1 (loopStartVon staleBild)) = some (BitVec.ofNat 64 (4096 + 21)) ∧
      ausgangRip (laufBytesI 1 (loopStartVon (bild staleWs staleProg))) =
        some (BitVec.ofNat 64 (4096 + 17)) := by
  decide

/-- POISON (forged width vector): the far jump marked rel8 does not
    validate. -/
theorem gift_breite : layoutOk (true :: List.replicate 14 false) fernProg = false := by
  decide

/-- POISON (raw control flow as an ordinary row): a pilot jump or a call
    written as an `op` bypasses the labels and is refused. -/
theorem gift_roher_sprung :
    relax 3 [.op (.pilot (.jump32 0))] = none ∧
      relax 3 [.op (.compact (.jump8 0))] = none ∧
      relax 3 [.op (.pilot (.call32 0))] = none := by
  decide

/- CUTS (what is NOT proved here):
   - The witnesses are concrete programs and runs checked by kernel
     evaluation; they add no generic claim beyond `ISARelax.lean`.
   - The original block program's semantics (`laufB`) and the byte run are
     compared at the observation (`loopBeob`) and through the generic
     `uebersetze_bytes`; the original program is never laid out in bytes.
   - The stale-displacement probe is the hazard a relaxation pass must
     avoid (recompute every displacement after any compression); with only
     shrinking branches no compression invalidates another branch's RANGE,
     so the probe forges the BYTES, which is what an unsound pass would emit.
-/

#print axioms loop_waehle
#print axioms loop_flach
#print axioms loop_relax
#print axioms loop_sprung
#print axioms loop_uebersetze
#print axioms loop_quelle
#print axioms loop_bytes
#print axioms loop_vorher
#print axioms loop_wx
#print axioms loop_code
#print axioms loop_flach_lauf
#print axioms relax_laufBytes_zeuge
#print axioms spurAn_layoutL_zeuge
#print axioms waehleB_korrekt_zeuge
#print axioms uebersetze_bytes_zeuge
#print axioms fern_bleibt_weit
#print axioms fern_lauf
#print axioms fern_wx
#print axioms fern_code
#print axioms fern_zeuge
#print axioms gift_verschiebung
#print axioms gift_label_aussen
#print axioms gift_veraltet
#print axioms gift_breite
#print axioms gift_roher_sprung

end Gabbro.Grammatik.X86
