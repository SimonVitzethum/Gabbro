/-
  File:      Grammatik/X86/ParallelMoves.lean
  Subject:   Parallel register moves lowered to sequential canonical movReg64 steps.

  Consumer: register allocation (IR-VALIDIERUNG.md, DIRECT-COMPILER-DESIGN.md
  §ABI): a parallel copy at a control-flow join or call boundary becomes a
  sequential `movReg64` list, with a 2-cycle broken through an explicit
  scratch register. Everything executes through the CANONICAL `schritt`/`lauf`
  of `Ausfuehrung.lean`: no second evaluator, no duplicated move semantics.
  Scratch is never free: every cycle theorem names the scratch, demands it
  distinct from both payload registers, and pins its clobbered value.
-/
import Grammatik.X86.Ausfuehrung

namespace Gabbro.Grammatik.X86

/-- One parallel-copy edge: the destination holds the source at the move point. -/
abbrev PMove := Register × Register

/-- One edge as a canonical decoded instruction (length 3, the Codec length). -/
def moveInstr (m : PMove) : Decodiert := ⟨.movReg64 m.1 m.2, 3⟩

/-- A parallel move list expanded to sequential canonical instructions. -/
def expandMoves (ms : List PMove) : List Decodiert := ms.map moveInstr

/-- Swap of `a` and `b` through scratch `t`: save, overwrite, restore. -/
def swapMitScratch (a b t : Register) : List Decodiert :=
  expandMoves [(t, a), (a, b), (b, t)]

/-- Every expanded edge carries a valid decode length. -/
theorem moveInstr_laenge (m : PMove) :
    laengeOk (moveInstr m).laenge = true := by
  cases m with
  | mk dst src => rfl

/-! ## Single-edge steps through the canonical `schritt`. -/

/-- One expanded edge steps exactly as the canonical register `mov`. -/
theorem schritt_moveInstr (m : PMove) (s : Zustand) :
    schritt (moveInstr m) s =
      some (schrittRegister s (ripNach s.rip 3) s.flags m.1
        (s.register m.2)) := by
  obtain ⟨dst, src⟩ := m
  exact schritt_movReg64 _ _ _ _ rfl rfl

/-- One expanded edge changes no memory byte (canonical `mov` frame). -/
theorem moveInstr_speicher (m : PMove) (s s' : Zustand)
    (hstep : schritt (moveInstr m) s = some s') :
    s'.speicher = s.speicher := by
  obtain ⟨dst, src⟩ := m
  exact schritt_movReg64_speicher _ _ _ _ _ rfl rfl hstep

/-- One expanded edge preserves the flags (canonical `mov` frame). -/
theorem moveInstr_flags (m : PMove) (s s' : Zustand)
    (hstep : schritt (moveInstr m) s = some s') :
    s'.flags = s.flags := by
  obtain ⟨dst, src⟩ := m
  exact schritt_movReg64_flags _ _ _ _ _ rfl rfl hstep

/-- One expanded edge delivers the source value to the destination. -/
theorem moveInstr_ziel (m : PMove) (s s' : Zustand)
    (hstep : schritt (moveInstr m) s = some s') :
    s'.register m.1 = s.register m.2 := by
  obtain ⟨dst, src⟩ := m
  have h := schritt_moveInstr (dst, src) s
  rw [h] at hstep
  cases hstep
  exact regSet_gleich _ _ _

/-- One expanded edge keeps every other register. -/
theorem moveInstr_fremd (m : PMove) (q : Register) (s s' : Zustand)
    (hq : q ≠ m.1)
    (hstep : schritt (moveInstr m) s = some s') :
    s'.register q = s.register q := by
  obtain ⟨dst, src⟩ := m
  simp only at hq
  have h := schritt_moveInstr (dst, src) s
  rw [h] at hstep
  cases hstep
  exact regSet_fremd _ _ _ _ hq

/-! ## Reached-run decomposition over the canonical `lauf`. -/

/-- A reached cons run yields its first step plus the reached rest. -/
theorem lauf_kopf (d : Decodiert) (rest : List Decodiert) (s s' : Zustand)
    (h : lauf (d :: rest) s = some s') :
    ∃ s1, schritt d s = some s1 ∧ lauf rest s1 = some s' := by
  simp only [lauf] at h
  generalize schritt d s = o at h ⊢
  cases o with
  | none => simp at h
  | some s1 =>
    simp only at h
    exact ⟨s1, rfl, h⟩

/-- A reached singleton run is its single step (from `lauf_kopf`, light:
    only small-constructor steps remain). -/
theorem lauf_einzeln (d : Decodiert) (s s' : Zustand)
    (h : lauf [d] s = some s') : schritt d s = some s' := by
  obtain ⟨a, h1, h2⟩ := lauf_kopf d [] s s' h
  simp only [lauf] at h2
  cases h2
  exact h1

/-! ## Whole-sequence frames by induction over the edge list. -/

/-- An expanded sequence changes no memory byte. -/
theorem expandMoves_speicher (ms : List PMove) (s s' : Zustand)
    (h : lauf (expandMoves ms) s = some s') :
    s'.speicher = s.speicher := by
  induction ms generalizing s with
  | nil =>
    simp only [expandMoves, List.map_nil, lauf] at h
    cases h
    rfl
  | cons m ms ih =>
    simp only [expandMoves, List.map_cons] at h
    obtain ⟨s1, h1, r1⟩ := lauf_kopf _ _ _ _ h
    have e1 : s1.speicher = s.speicher := moveInstr_speicher m s s1 h1
    have e2 : s'.speicher = s1.speicher := ih s1 r1
    rw [e2, e1]

/-- An expanded sequence preserves the flags. -/
theorem expandMoves_flags (ms : List PMove) (s s' : Zustand)
    (h : lauf (expandMoves ms) s = some s') :
    s'.flags = s.flags := by
  induction ms generalizing s with
  | nil =>
    simp only [expandMoves, List.map_nil, lauf] at h
    cases h
    rfl
  | cons m ms ih =>
    simp only [expandMoves, List.map_cons] at h
    obtain ⟨s1, h1, r1⟩ := lauf_kopf _ _ _ _ h
    have e1 : s1.flags = s.flags := moveInstr_flags m s s1 h1
    have e2 : s'.flags = s1.flags := ih s1 r1
    rw [e2, e1]

/-! ## Swap through an explicit scratch register. -/

/-- The swap shape unfolds to its three canonical edges. -/
theorem swapMitScratch_entfaltet (a b t : Register) :
    swapMitScratch a b t =
      [moveInstr (t, a), moveInstr (a, b), moveInstr (b, t)] := by
  rfl

/-- Swap through a distinct scratch: the payloads exchange values.
    Every alias premise is load-bearing: `hbt` keeps `b` across the save,
    `hat` keeps `t` across the overwrite, `hab` keeps `a` across the restore. -/
theorem swap_tausch (a b t : Register) (s s' : Zustand)
    (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t)
    (hstep : lauf (swapMitScratch a b t) s = some s') :
    s'.register a = s.register b ∧ s'.register b = s.register a := by
  rw [swapMitScratch_entfaltet] at hstep
  obtain ⟨s1, h1, r1⟩ := lauf_kopf _ _ _ _ hstep
  obtain ⟨s2, h2, r2⟩ := lauf_kopf _ _ _ _ r1
  have h3 : schritt (moveInstr (b, t)) s2 = some s' := lauf_einzeln _ _ _ r2
  have e1 : s1.register t = s.register a := moveInstr_ziel _ _ _ h1
  have e2 : s2.register a = s1.register b := moveInstr_ziel _ _ _ h2
  have e3 : s'.register b = s2.register t := moveInstr_ziel _ _ _ h3
  have f1 : s1.register b = s.register b := moveInstr_fremd _ _ _ _ hbt h1
  have f2 : s2.register t = s1.register t :=
    moveInstr_fremd _ _ _ _ (Ne.symm hat) h2
  have f3 : s'.register a = s2.register a := moveInstr_fremd _ _ _ _ hab h3
  exact ⟨by rw [f3, e2, f1], by rw [e3, f2, e1]⟩

/-- The scratch register is destroyed: it ends holding the old `a` value.
    Liveness obligation for the allocator: `t` must be dead after the swap. -/
theorem swap_scratch_belegt (a b t : Register) (s s' : Zustand)
    (hat : a ≠ t) (hbt : b ≠ t)
    (hstep : lauf (swapMitScratch a b t) s = some s') :
    s'.register t = s.register a := by
  rw [swapMitScratch_entfaltet] at hstep
  obtain ⟨s1, h1, r1⟩ := lauf_kopf _ _ _ _ hstep
  obtain ⟨s2, h2, r2⟩ := lauf_kopf _ _ _ _ r1
  have h3 : schritt (moveInstr (b, t)) s2 = some s' := lauf_einzeln _ _ _ r2
  have e1 : s1.register t = s.register a := moveInstr_ziel _ _ _ h1
  have f2 : s2.register t = s1.register t :=
    moveInstr_fremd _ _ _ _ (Ne.symm hat) h2
  have g : s'.register t = s2.register t :=
    moveInstr_fremd _ _ _ _ (Ne.symm hbt) h3
  rw [g, f2, e1]

/-- The swap keeps every uninvolved register. -/
theorem swap_rahmen (a b t : Register) (q : Register) (s s' : Zustand)
    (hqa : q ≠ a) (hqb : q ≠ b) (hqt : q ≠ t)
    (hstep : lauf (swapMitScratch a b t) s = some s') :
    s'.register q = s.register q := by
  rw [swapMitScratch_entfaltet] at hstep
  obtain ⟨s1, h1, r1⟩ := lauf_kopf _ _ _ _ hstep
  obtain ⟨s2, h2, r2⟩ := lauf_kopf _ _ _ _ r1
  have h3 : schritt (moveInstr (b, t)) s2 = some s' := lauf_einzeln _ _ _ r2
  have g1 : s1.register q = s.register q := moveInstr_fremd _ _ _ _ hqt h1
  have g2 : s2.register q = s1.register q := moveInstr_fremd _ _ _ _ hqa h2
  have g3 : s'.register q = s2.register q := moveInstr_fremd _ _ _ _ hqb h3
  rw [g3, g2, g1]

/-- The swap changes no memory byte and preserves the flags. -/
theorem swap_speicher_flags (a b t : Register) (s s' : Zustand)
    (hstep : lauf (swapMitScratch a b t) s = some s') :
    s'.speicher = s.speicher ∧ s'.flags = s.flags :=
  ⟨expandMoves_speicher _ _ _ hstep, expandMoves_flags _ _ _ hstep⟩

/-! ## Joint witness and alias counterexamples, by canonical evaluation. -/

/-- Witness register file: `rax = 7`, `rbx = 9`, stack top at 8192. -/
def tauschZeugeReg : Register → Wort :=
  fun q =>
    if q = Register.rax then BitVec.ofNat 64 7
    else if q = Register.rbx then BitVec.ofNat 64 9
    else zeugeReg q

/-- Witness start state: distinct payloads, zeroed readable/writable memory. -/
def tauschZeuge : Zustand :=
  { register := tauschZeugeReg, flags := zeugeFlags,
    rip := BitVec.ofNat 64 4096, speicher := zeugeSpeicher }

/-- Witness program: a memory-changing prefix (`movImm` + `store` through
    the stack pointer) followed by the canonical `rax`/`rbx` swap through
    scratch `r10`. -/
def tauschZeugeProg : List Decodiert :=
  [{ befehl := Befehl.movImm64 Register.rcx (BitVec.ofNat 64 42), laenge := 3 },
   { befehl := Befehl.store64 Register.rsp Register.rcx (BitVec.ofNat 32 0),
     laenge := 4 },
   { befehl := Befehl.movReg64 Register.r10 Register.rax, laenge := 3 },
   { befehl := Befehl.movReg64 Register.rax Register.rbx, laenge := 3 },
   { befehl := Befehl.movReg64 Register.rbx Register.r10, laenge := 3 }]

/-- Joint witness: a REACHED run whose prefix observably changes memory
    (byte `0x00` becomes `42` at the stack top) and whose suffix swaps the
    payload registers; the scratch ends holding the old `rax` value. -/
theorem tausch_zeuge :
    ((lauf tauschZeugeProg tauschZeuge).map
        (fun s => (s.register Register.rax, s.register Register.rbx)) =
      some (BitVec.ofNat 64 9, BitVec.ofNat 64 7)) ∧
    ((lauf tauschZeugeProg tauschZeuge).map
        (fun s => s.speicher.bytes (BitVec.ofNat 64 8192)) =
      some (BitVec.ofNat 8 42)) ∧
    (tauschZeuge.speicher.bytes (BitVec.ofNat 64 8192) =
      BitVec.ofNat 8 0) ∧
    ((lauf tauschZeugeProg tauschZeuge).map
        (fun s => s.register Register.r10) =
      some (BitVec.ofNat 64 7)) := by
  decide

/-- Negative case: the naive scratch-free "swap" `[rax<-rbx, rbx<-rax]`
    loses a value (both end holding the old `rbx`), so it is no swap. -/
theorem naiv_ohne_scratch_verliert :
    ((lauf [⟨Befehl.movReg64 Register.rax Register.rbx, 3⟩,
      ⟨Befehl.movReg64 Register.rbx Register.rax, 3⟩] tauschZeuge).map
        (fun s => (s.register Register.rax, s.register Register.rbx)) =
      some (BitVec.ofNat 64 9, BitVec.ofNat 64 9)) ∧
    ((lauf [⟨Befehl.movReg64 Register.rax Register.rbx, 3⟩,
      ⟨Befehl.movReg64 Register.rbx Register.rax, 3⟩] tauschZeuge).map
        (fun s => (s.register Register.rax, s.register Register.rbx)) ≠
      some (BitVec.ofNat 64 9, BitVec.ofNat 64 7)) := by
  decide

/-- Negative case: a scratch that aliases the first payload (`t = a`)
    loses a value as well (both end holding the old `rbx`). -/
theorem falscher_scratch_verliert :
    ((lauf (swapMitScratch Register.rax Register.rbx Register.rax)
      tauschZeuge).map
        (fun s => (s.register Register.rax, s.register Register.rbx)) =
      some (BitVec.ofNat 64 9, BitVec.ofNat 64 9)) ∧
    ((lauf (swapMitScratch Register.rax Register.rbx Register.rax)
      tauschZeuge).map
        (fun s => (s.register Register.rax, s.register Register.rbx)) ≠
      some (BitVec.ofNat 64 9, BitVec.ofNat 64 7)) := by
  decide

/- CUTS:
   - Proved: edge expansion to canonical `movReg64` with per-edge frames,
     `lauf` head/singleton decomposition, whole-sequence memory/flag frames,
     the 2-cycle swap through an explicit distinct scratch (payload exchange,
     scratch clobber, uninvolved-register frame, memory/flag preservation),
     a joint reached witness with a memory-changing prefix, and two decided
     alias counterexamples. What is NOT here:
   - No general n-cycle scheduling: only the 2-cycle with one caller-provided
     scratch is proved; longer cycles, chained copies and copy-propagation
     orderings have no theorem (no liveness analysis, no allocator).
   - No free scratch: the scratch is a named premise, proved destroyed; no
     theorem conjures a dead register, and deadness at the program point is
     the allocator's proof obligation, not stated here.
   - Only `movReg64` is expanded: narrow widths, immediates, memory operands
     and flags-affecting forms have no parallel-move rule.
   - No decoder, encoder, TSO bridge, concurrency, source correspondence,
     contract, cost, timing, progress or whole-image claim: `lauf` is a
     sequential fold over checked lengths, and RIP advance is not a timing
     statement.
   - No per-access atomicity: an eight-byte `mov` is one sequential register
     step here; tearing under concurrency stays with the TSO-bridge lane.
-/

#print axioms moveInstr_laenge
#print axioms schritt_moveInstr
#print axioms moveInstr_speicher
#print axioms moveInstr_flags
#print axioms moveInstr_ziel
#print axioms moveInstr_fremd
#print axioms lauf_kopf
#print axioms lauf_einzeln
#print axioms expandMoves_speicher
#print axioms expandMoves_flags
#print axioms swapMitScratch_entfaltet
#print axioms swap_tausch
#print axioms swap_scratch_belegt
#print axioms swap_rahmen
#print axioms swap_speicher_flags
#print axioms tausch_zeuge
#print axioms naiv_ohne_scratch_verliert
#print axioms falscher_scratch_verliert

end Gabbro.Grammatik.X86
