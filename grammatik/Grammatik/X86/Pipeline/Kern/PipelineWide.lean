/-
  File:      Grammatik/X86/PipelineWide.lean
  Subject:   Pipeline lowering onto the wider ISA: the 14-form pilot
             program selects compact imm/disp forms (`kompaktWahl`) with
             an exact-equivalence check on the observable against the
             pilot lowering, plus decided refusals for everything else.

  Reused, not duplicated:
    - `kompaktWahl`/`kernGleich`/`schrittC`/`encodeC` and the selector
      correctness theorems (`CompactForms.lean`);
    - `aluImmWahl`/`aluImmWahl_korrekt_imm8`
      (`CompactFormsWitnesses.lean`);
    - `OptRel`/`optRel_bind` (`ISASelect.lean`);
    - `schritt`/`lauf`/`kanon`-style lengths, step equations and the
      witness state (`Ausfuehrung.lean`, `Codec.lean`).
  No second IR, no second source interpreter, no change to any
  existing file except the one import line in `Grammatik.lean`.
-/
import Grammatik.X86.Befehle.Kompakt.CompactForms
import Grammatik.X86.Befehle.Kompakt.CompactFormsWitnesses
import Grammatik.X86.Befehle.ISA.ISASelect
import Grammatik.X86.Kern.Ausfuehrung
import Grammatik.X86.Kern.Codec
import Grammatik.X86.Quelle.ExpressionLowering
namespace Gabbro.Grammatik.X86.PipelineWide

open Gabbro.Grammatik
open Gabbro.Grammatik.X86

/-- Decided coverage: the three data-moving pilot forms whose compact
    selection carries the `kernGleich` (registers, flags, memory)
    correctness. Jumps need layout relaxation; the other nine pilot
    forms have no compact analog at all. -/
def wideDatOk : Befehl → Bool
  | .movImm64 _ _ | .load64 _ _ _ | .store64 _ _ _ => true
  | _ => false

/-- The canonical compact decoding, mirroring `Pipeline.kanon`. -/
def kanonW (cb : CompactBefehl) : CompactDecodiert :=
  ⟨cb, (encodeC cb).length⟩

/-- Every canonical compact length passes the shared length guard
    (same proof shape as `ISA.encodeC_len`, from `encodeC` itself). -/
theorem kanonW_ok (cb : CompactBefehl) :
    laengeOk (kanonW cb).laenge = true := by
  simp only [laengeOk, kanonW]
  cases cb <;> simp only [encodeC, leBytes32] <;> (try split) <;> simp

/-- Literal-form length guard, for rewriting under canonical decodings. -/
theorem kanonW_len (cb : CompactBefehl) :
    laengeOk (encodeC cb).length = true := kanonW_ok cb

/-- THE DECIDED PER-INSTRUCTION VALIDATOR: the compact form is
    exactly the selector's choice for this pilot instruction, and the
    instruction is in the covered data-moving fragment. -/
def wideOk (b : Befehl) (cb : CompactBefehl) : Bool :=
  decide (kompaktWahl b = some cb) && wideDatOk b

theorem wideOk_teile (b : Befehl) (cb : CompactBefehl)
    (h : wideOk b cb = true) :
    kompaktWahl b = some cb ∧ wideDatOk b = true := by
  unfold wideOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h

/-- Whole-program selection: every pilot instruction maps through the
    decided validator; anything else is refused with `none`. -/
def wideSelect : List Befehl → Option (List CompactBefehl)
  | [] => some []
  | b :: rest =>
    if wideDatOk b then
      match kompaktWahl b, wideSelect rest with
      | some cb, some w => some (cb :: w)
      | _, _ => none
    else none

/-- The compact run, mirroring `Ausfuehrung.lauf`. -/
def laufW : List CompactDecodiert → Zustand → Option Zustand
  | [], s => some s
  | d :: rest, s => match schrittC d s with
    | some s' => laufW rest s'
    | none => none

/-- THE EXACT-EQUIVALENCE CHECK, SINGLE STEP: a validated compact
    instruction runs exactly like its pilot instruction on the
    observable (registers, claimed flags, memory, by `kernGleich`),
    from any two states that already agree there. Lengths are the two
    canonical ones; RIP is excluded on both sides. -/
theorem wideSchritt (b : Befehl) (cb : CompactBefehl) (s1 s2 : Zustand)
    (hok : wideOk b cb = true) (hg : kernGleich s1 s2) :
    OptRel kernGleich
      (schritt ⟨b, (encode b).length⟩ s1)
      (schrittC ⟨cb, (encodeC cb).length⟩ s2) := by
  obtain ⟨hsel, hcov⟩ := wideOk_teile b cb hok
  cases b with
  | movImm64 dst v =>
    simp only [kompaktWahl] at hsel
    split at hsel
    · rename_i hzx
      cases hsel
      have hv : zextWort32 (BitVec.ofNat 32 v.toNat) = v :=
        of_decide_eq_true hzx
      rw [schritt_movImm64 _ _ dst v (laengeOk_encode _) rfl]
      rw [schrittC_movImm32Zx _ _ dst _ (kanonW_len _) rfl]
      rw [hv]
      simp only [OptRel]
      exact ⟨by show regSet s1.register dst v = regSet s2.register dst v; rw [hg.1],
        hg.2.1, hg.2.2⟩
    · split at hsel
      · rename_i hneg hsx
        cases hsel
        have hv : dispWort (BitVec.ofNat 32 v.toNat) = v :=
          of_decide_eq_true hsx
        rw [schritt_movImm64 _ _ dst v (laengeOk_encode _) rfl]
        rw [schrittC_movImm32Sx _ _ dst _ (kanonW_len _) rfl]
        rw [hv]
        simp only [OptRel]
        exact ⟨by show regSet s1.register dst v = regSet s2.register dst v; rw [hg.1],
          hg.2.1, hg.2.2⟩
      · simp at hsel
  | load64 dst base disp =>
    simp only [kompaktWahl] at hsel
    split at hsel
    · rename_i hd0
      cases hsel
      have hdisp : disp = 0 := (of_decide_eq_true hd0).1
      have haddr0 : effAddr0 s2 base = effAddr s2 base 0 :=
        effAddr0_eq_effAddr s2 base
      have hreg : effAddr s1 base disp = effAddr s2 base disp := by
        unfold effAddr; rw [hg.1]
      cases hrd : read64 s1.speicher (effAddr s1 base disp) with
      | none =>
        have hrd2 : read64 s2.speicher (effAddr0 s2 base) = none := by
          rw [haddr0, ← hdisp, ← hreg, ← hg.2.2]; exact hrd
        rw [schritt_load64_verweigert _ _ dst base disp (laengeOk_encode _) rfl hrd]
        rw [schrittC_load64Disp0_verweigert _ _ dst base (kanonW_len _) rfl hrd2]
        simp only [OptRel]
      | some v =>
        have hrd2 : read64 s2.speicher (effAddr0 s2 base) = some v := by
          rw [haddr0, ← hdisp, ← hreg, ← hg.2.2]; exact hrd
        rw [schritt_load64_erfolg _ _ dst base disp v (laengeOk_encode _) rfl hrd]
        rw [schrittC_load64Disp0_erfolg _ _ dst base v (kanonW_len _) rfl hrd2]
        simp only [OptRel]
        exact ⟨by show regSet s1.register dst v = regSet s2.register dst v; rw [hg.1],
          hg.2.1, hg.2.2⟩
    · split at hsel
      · rename_i hneg hs8
        cases hsel
        have haddr : effAddr8 s2 base (disp8Of disp) = effAddr s2 base disp := by
          rw [effAddr8_eq_effAddr, of_decide_eq_true hs8]
        have hreg : effAddr s1 base disp = effAddr s2 base disp := by
          unfold effAddr; rw [hg.1]
        cases hrd : read64 s1.speicher (effAddr s1 base disp) with
        | none =>
          have hrd2 : read64 s2.speicher (effAddr8 s2 base (disp8Of disp)) = none := by
            rw [haddr, ← hreg, ← hg.2.2]; exact hrd
          rw [schritt_load64_verweigert _ _ dst base disp (laengeOk_encode _) rfl hrd]
          rw [schrittC_load64Disp8_verweigert _ _ dst base (disp8Of disp) (kanonW_len _) rfl hrd2]
          simp only [OptRel]
        | some v =>
          have hrd2 : read64 s2.speicher (effAddr8 s2 base (disp8Of disp)) = some v := by
            rw [haddr, ← hreg, ← hg.2.2]; exact hrd
          rw [schritt_load64_erfolg _ _ dst base disp v (laengeOk_encode _) rfl hrd]
          rw [schrittC_load64Disp8_erfolg _ _ dst base (disp8Of disp) v (kanonW_len _) rfl hrd2]
          simp only [OptRel]
          exact ⟨by show regSet s1.register dst v = regSet s2.register dst v; rw [hg.1],
            hg.2.1, hg.2.2⟩
      · simp at hsel
  | store64 base src disp =>
    simp only [kompaktWahl] at hsel
    split at hsel
    · rename_i hd0
      cases hsel
      have hdisp : disp = 0 := (of_decide_eq_true hd0).1
      have haddr0 : effAddr0 s2 base = effAddr s2 base 0 :=
        effAddr0_eq_effAddr s2 base
      have hreg : effAddr s1 base disp = effAddr s2 base disp := by
        unfold effAddr; rw [hg.1]
      have hsrc : s1.register src = s2.register src := by rw [hg.1]
      cases hwr : write64 s1.speicher (effAddr s1 base disp) (s1.register src) with
      | none =>
        have hwr2 : write64 s2.speicher (effAddr0 s2 base) (s2.register src) = none := by
          rw [haddr0, ← hdisp, ← hreg, ← hg.2.2, ← hsrc]; exact hwr
        rw [schritt_store64_verweigert _ _ base src disp (laengeOk_encode _) rfl hwr]
        rw [schrittC_store64Disp0_verweigert _ _ base src (kanonW_len _) rfl hwr2]
        simp only [OptRel]
      | some m =>
        have hwr2 : write64 s2.speicher (effAddr0 s2 base) (s2.register src) = some m := by
          rw [haddr0, ← hdisp, ← hreg, ← hg.2.2, ← hsrc]; exact hwr
        rw [schritt_store64_erfolg _ _ base src disp m (laengeOk_encode _) rfl hwr]
        rw [schrittC_store64Disp0_erfolg _ _ base src m (kanonW_len _) rfl hwr2]
        simp only [OptRel]
        exact ⟨hg.1, hg.2.1, rfl⟩
    · split at hsel
      · rename_i hneg hs8
        cases hsel
        have haddr : effAddr8 s2 base (disp8Of disp) = effAddr s2 base disp := by
          rw [effAddr8_eq_effAddr, of_decide_eq_true hs8]
        have hreg : effAddr s1 base disp = effAddr s2 base disp := by
          unfold effAddr; rw [hg.1]
        have hsrc : s1.register src = s2.register src := by rw [hg.1]
        cases hwr : write64 s1.speicher (effAddr s1 base disp) (s1.register src) with
        | none =>
          have hwr2 : write64 s2.speicher (effAddr8 s2 base (disp8Of disp)) (s2.register src) = none := by
            rw [haddr, ← hreg, ← hg.2.2, ← hsrc]; exact hwr
          rw [schritt_store64_verweigert _ _ base src disp (laengeOk_encode _) rfl hwr]
          rw [schrittC_store64Disp8_verweigert _ _ base src (disp8Of disp) (kanonW_len _) rfl hwr2]
          simp only [OptRel]
        | some m =>
          have hwr2 : write64 s2.speicher (effAddr8 s2 base (disp8Of disp)) (s2.register src) = some m := by
            rw [haddr, ← hreg, ← hg.2.2, ← hsrc]; exact hwr
          rw [schritt_store64_erfolg _ _ base src disp m (laengeOk_encode _) rfl hwr]
          rw [schrittC_store64Disp8_erfolg _ _ base src (disp8Of disp) m (kanonW_len _) rfl hwr2]
          simp only [OptRel]
          exact ⟨hg.1, hg.2.1, rfl⟩
      · simp at hsel
  | movReg64 _ _ => simp [wideDatOk] at hcov
  | addReg64 _ _ => simp [wideDatOk] at hcov
  | subReg64 _ _ => simp [wideDatOk] at hcov
  | xorReg64 _ _ => simp [wideDatOk] at hcov
  | cmpReg64 _ _ => simp [wideDatOk] at hcov
  | jump32 _ => simp [wideDatOk] at hcov
  | jumpIf32 _ _ => simp [wideDatOk] at hcov
  | call32 _ => simp [wideDatOk] at hcov
  | push64 _ => simp [wideDatOk] at hcov
  | pop64 _ => simp [wideDatOk] at hcov
  | ret => simp [wideDatOk] at hcov

/-- The canonical pilot decoding, mirroring `Pipeline.kanon`. -/
def kanonP (b : Befehl) : Decodiert := ⟨b, (encode b).length⟩

/-- Every canonical pilot length passes the shared length guard
    (reused `ExpressionLowering.laengeOk_encode`). -/
theorem kanonP_ok (b : Befehl) : laengeOk (kanonP b).laenge = true :=
  laengeOk_encode b

/-- A successful whole-program selection starts with a validated
    head pair and a successful tail selection. -/
theorem wideSelect_cons (b : Befehl) (rest : List Befehl)
    (wide : List CompactBefehl) (h : wideSelect (b :: rest) = some wide) :
    ∃ cb w, wideOk b cb = true ∧ wideSelect rest = some w ∧ wide = cb :: w := by
  unfold wideSelect at h
  by_cases hcov : wideDatOk b = true
  · rw [if_pos hcov] at h
    cases hcb : kompaktWahl b with
    | none => simp [hcb] at h
    | some cb =>
      cases hr : wideSelect rest with
      | none => simp [hcb, hr] at h
      | some w =>
        simp [hcb, hr] at h
        cases h
        exact ⟨cb, w, by unfold wideOk; simp [hcb, hcov], rfl, rfl⟩
  · rw [if_neg hcov] at h
    cases h

/-- A pilot run of `d :: ds` is one step, then the rest
    (bind-bridge for the reused `optRel_bind` sequencer). -/
theorem lauf_cons (d : Decodiert) (ds : List Decodiert) (s : Zustand) :
    lauf (d :: ds) s = (schritt d s).bind (lauf ds) := by
  simp only [lauf]
  cases schritt d s <;> rfl

/-- A compact run of `d :: ds` is one step, then the rest. -/
theorem laufW_cons (d : CompactDecodiert) (ds : List CompactDecodiert) (s : Zustand) :
    laufW (d :: ds) s = (schrittC d s).bind (laufW ds) := by
  simp only [laufW]
  cases schrittC d s <;> rfl

/-- **WIDE-LOWERING CORRECTNESS FOR WHOLE RUNS.** A successfully
    selected compact program runs exactly like the pilot program on
    the observable (registers, claimed flags, memory): both refuse,
    or both succeed with agreeing successors. RIP is excluded on
    both sides (the compact program is shorter); proved by induction
    with the reused `optRel_bind` sequencer and `wideSchritt`. -/
theorem wideSelect_korrekt (prog : List Befehl) :
    ∀ (wide : List CompactBefehl) (s1 s2 : Zustand),
    wideSelect prog = some wide → kernGleich s1 s2 →
    OptRel kernGleich (lauf (prog.map kanonP) s1) (laufW (wide.map kanonW) s2) := by
  induction prog with
  | nil =>
    intro wide s1 s2 hsel hg
    simp only [wideSelect] at hsel
    cases hsel
    simpa [lauf, laufW, OptRel] using hg
  | cons b rest ih =>
    intro wide s1 s2 hsel hg
    obtain ⟨cb, w, hval, hrest, rfl⟩ := wideSelect_cons b rest wide hsel
    simp only [List.map_cons, lauf_cons, laufW_cons]
    exact optRel_bind kernGleich kernGleich _ _
      _ _ (wideSchritt b cb s1 s2 hval hg)
      (fun a b2 hab => ih w a b2 hrest hab)

/-- POISON (no compact analog): a register-register add is refused. -/
theorem wideSelect_refuses_add :
    wideSelect [.addReg64 .rax .rcx] = none := by decide

/-- POISON (no compact analog): a stack push is refused. -/
theorem wideSelect_refuses_push :
    wideSelect [.push64 .rax] = none := by decide

/-- POISON (layout scope): a jump is refused even where the branch
    selector would succeed -- target preservation needs the layout's
    bounded relaxation, which this file does not run. -/
theorem wideSelect_refuses_jump :
    wideSelect [.jump32 (BitVec.ofNat 32 0)] = none := by decide

/-- POISON (unrepresentable immediate): `0x100000001` is neither
    zero- nor sign-extended from its low 32 bits. -/
theorem wideSelect_refuses_imm :
    wideSelect [.movImm64 .rax (BitVec.ofNat 64 0x100000001)] = none := by decide

/-- POISON (both memory refusals at once): `rbp`-relative disp0 is
    the RIP-relative special case, and 200 is outside the signed
    8-bit displacement range. -/
theorem wideSelect_refuses_rbp :
    wideSelect [.load64 .rax .rbp (BitVec.ofNat 32 200)] = none := by decide

/-- POISON (tail refusal): a covered head does not save a refused tail. -/
theorem wideSelect_refuses_tail :
    wideSelect [.movImm64 .rax 5, .addReg64 .rax .rcx] = none := by decide

/-- Bind elimination: a successful projected run yields the reached
    state and its projection. -/
theorem bind_some_elim {α β : Type} {m : Option α} {f : α → Option β} {y : β}
    (h : m.bind f = some y) : ∃ x, m = some x ∧ f x = some y := by
  cases m with
  | none => rw [Option.bind_none] at h; cases h
  | some x => exact ⟨x, rfl, h⟩

/-- **WITNESS (`wideSelect_korrekt_zeuge`).** The store program
    selects, both runs reach a memory-changing step on the shared
    witness state (`cwZustand`: RAX holds 10, the stack top is 8192,
    memory is zeroed): the stored word reads back as 10 at
    `rsp + 8 = 8200` on both sides while the initial byte there is 0,
    and the two successors agree on the observable. -/
theorem wideSelect_korrekt_zeuge :
    ∃ (w : List CompactBefehl) (s1' s2' : Zustand),
      wideSelect [.store64 .rsp .rax (BitVec.ofNat 32 8)] = some w ∧
      lauf ([.store64 .rsp .rax (BitVec.ofNat 32 8)].map kanonP) cwZustand = some s1' ∧
      laufW (w.map kanonW) cwZustand = some s2' ∧
      kernGleich s1' s2' ∧
      read64 s1'.speicher (BitVec.ofNat 64 8200) = some 10 ∧
      cwZustand.speicher.bytes (BitVec.ofNat 64 8200) = 0 := by
  have hsel : wideSelect [.store64 .rsp .rax (BitVec.ofNat 32 8)] =
      some [.store64Disp8 .rsp .rax (BitVec.ofNat 8 8)] := by decide
  have hr1 : ((lauf ([.store64 .rsp .rax (BitVec.ofNat 32 8)].map kanonP)
      cwZustand).bind (fun s => read64 s.speicher (BitVec.ofNat 64 8200))) =
      some 10 := by decide
  have hr2 : ((laufW ([.store64Disp8 .rsp .rax (BitVec.ofNat 8 8)].map kanonW)
      cwZustand).bind (fun s => read64 s.speicher (BitVec.ofNat 64 8200))) =
      some 10 := by decide
  have hbyte : cwZustand.speicher.bytes (BitVec.ofNat 64 8200) = 0 := by decide
  obtain ⟨s1', hL, hr1'⟩ := bind_some_elim hr1
  obtain ⟨s2', hW, hr2'⟩ := bind_some_elim hr2
  have hcorr := wideSelect_korrekt [.store64 .rsp .rax (BitVec.ofNat 32 8)]
    [.store64Disp8 .rsp .rax (BitVec.ofNat 8 8)] cwZustand cwZustand hsel
    ⟨rfl, rfl, rfl⟩
  rw [hL, hW] at hcorr
  simp only [OptRel] at hcorr
  exact ⟨_, s1', s2', hsel, hL, hW, hcorr, hr1', hbyte⟩

/- CUTS (exactly what is NOT proved here):

   Covered. The three data-moving pilot forms (`movImm64`, `load64`,
   `store64`) select compact forms through the accepted `kompaktWahl`,
   with exact per-step (`wideSchritt`) and whole-run
   (`wideSelect_korrekt`) equivalence on registers, claimed flags and
   memory (`kernGleich`, RIP excluded). No flag-liveness premise is
   needed: the compact effects are EXACT, not abstractions.

   Refused, never guessed. The other nine pilot forms have no compact
   analog (`wideSelect_refuses_add`, `_push`); jumps are refused even
   where the branch selector would succeed, because target
   preservation needs the layout's bounded relaxation, which this
   file does not run (`wideSelect_refuses_jump`); unrepresentable
   immediates and displacements are refused by decision
   (`wideSelect_refuses_imm`, `_rbp`, `_tail`).

   Narrow widths. No lowering is stated: a 32-bit narrow op is not
   observable-equal to any 64-bit pilot op, so no exact-equivalence
   check on the observable can be written against the pilot
   lowering. A narrow bridge would need width-specific value and
   flag correspondence proofs, which are out of scope here.

   Multiply/divide, shifts, SETcc/CMOVcc. These live in
   `ExtendedExecution`'s `ExtInstr` over `FpZustand` and have NO pilot
   source form, so there is no pilot lowering to check a selection
   against. They stay refused. `aluImmWahl` (imm8-vs-imm32 inside
   the compact family) is reused as imported, with its own
   correctness proof; it is not wired as a pilot lowering because
   the pilot has no immediate-ALU form to select from.

   Not closed here. The source-`execBlock` leg stays with the pilot
   pipeline (`Pipeline`/`PipelineImage`/`PipelineEntry`): this file
   proves pilot-lowering vs wide-lowering run equivalence, which is
   the check the task asks for, not a second source-to-bytes chain.
   There is no byte-level fetch bridge for compact bytes (no
   `CodeAt`/`laufBytes` over `encodeC` programs); both runs use
   their canonical lengths (`kanonP_ok`, `kanonW_len`). No TSO, no
   time, no control flow admitted by selection, one core, model
   memory -- everything of the pilot pipeline's CUTS still applies. -/

#print axioms kanonW_ok
#print axioms kanonW_len
#print axioms wideOk_teile
#print axioms wideSchritt
#print axioms kanonP_ok
#print axioms wideSelect_cons
#print axioms lauf_cons
#print axioms laufW_cons
#print axioms wideSelect_korrekt
#print axioms bind_some_elim
#print axioms wideSelect_refuses_add
#print axioms wideSelect_refuses_push
#print axioms wideSelect_refuses_jump
#print axioms wideSelect_refuses_imm
#print axioms wideSelect_refuses_rbp
#print axioms wideSelect_refuses_tail
#print axioms wideSelect_korrekt_zeuge

end Gabbro.Grammatik.X86.PipelineWide
