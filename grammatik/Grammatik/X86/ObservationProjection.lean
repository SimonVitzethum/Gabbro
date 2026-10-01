/-
  File:      Grammatik/X86/ObservationProjection.lean
  Subject:   Canonical target observation projection with real faults/stops.

  Lane 433 (continuous Lean proof reserve): a focused canonical observation
  projection over the accepted pilot vocabulary (`Typen`, `Ausfuehrung`,
  `Byteschritt`). `Sichtbar` names the visible memory predicate and the live
  registers; `BeobGleich` equates RIP, flags, visible memory and live
  registers only. Dead registers stay hidden under an explicit liveness
  premise the consumer must establish per program point; timing and
  microarchitecture are never part of the projection. Refusal (`verweigert`)
  is observably distinct from success. No source, cost, call, I/O, TSO or
  hardware claim is made here.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Speicher
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Byteschritt

namespace Gabbro.Grammatik.X86

/-- Visible observation scope: the memory predicate the observer may read
    and the registers live at the observed point. Everything else (dead
    registers, timing, microarchitectural state) is hidden by construction. -/
structure Sichtbar where
  adr : Adresse → Bool
  lebendig : Register → Bool

/-- Observation equality: same control position, same flags, same visible
    memory bytes, same live registers. RIP and flags are INCLUDED: hiding
    them would equate states whose next fetch or branch observably differs. -/
def BeobGleich (V : Sichtbar) (s t : Zustand) : Prop :=
  s.rip = t.rip ∧ s.flags = t.flags ∧
    (∀ a, V.adr a = true → s.speicher.bytes a = t.speicher.bytes a) ∧
    (∀ r, V.lebendig r = true → s.register r = t.register r)

/-! ## Outcome projection: success and real fault/stop outcomes. -/

/-- Observable outcome over visible scope: `ok` carries the visible memory
    snapshot and the live register values; `fehler` is the coarse real
    fault/stop outcome (fetch refusal, failed memory access, bad length).
    Fault granularity beyond success/refusal (page fault vs decode fault,
    timing) is deliberately NOT distinguished: no false precision. -/
inductive Beobachtung where
  | ok : (mem : Adresse → Byte) → (regs : Register → Option Wort) → Beobachtung
  | fehler : Beobachtung

/-- State snapshot under visible scope: visible bytes kept, hidden bytes
    zeroed; live registers kept, dead registers mapped to `none`. -/
def beobSchnappschuss (V : Sichtbar) (s : Zustand) :
    (Adresse → Byte) × (Register → Option Wort) :=
  ((fun a => if V.adr a then s.speicher.bytes a else BitVec.ofNat 8 0),
   (fun r => if V.lebendig r then some (s.register r) else none))

/-- Outcome projection: a successful byte step shows its snapshot; a real
    fault/stop shows `fehler`, never `ok`. -/
def beobAusgang (V : Sichtbar) : ByteAusgang → Beobachtung
  | .weiter s =>
    .ok (beobSchnappschuss V s).1 (beobSchnappschuss V s).2
  | .verweigert => .fehler

/-- Executable outcome kind: `true` is success, `false` is a real
    fault/stop. Witnesses decide over this, never over state equality. -/
def beobKind : ByteAusgang → Bool
  | .weiter _ => true
  | .verweigert => false

/-- A refusal never projects to `ok`: faults/stops are observable. -/
theorem beobAusgang_verweigert (V : Sichtbar) :
    beobAusgang V .verweigert = .fehler := by
  rfl

/-- Success and refusal project differently: no fault is silent. -/
theorem beobAusgang_weiter_ungleich (V : Sichtbar) (s : Zustand) :
    beobAusgang V (.weiter s) ≠ .fehler := by
  simp [beobAusgang]

/-- Observation equality is reflexive. -/
theorem beobGleich_refl (V : Sichtbar) (s : Zustand) :
    BeobGleich V s s := by
  exact ⟨rfl, rfl, fun _ _ => rfl, fun _ _ => rfl⟩

/-! ## Executable single-point projections and concrete scope. -/

/-- Executable register projection: live registers show their value, dead
    (scratch) registers show `none` — hidden by construction. -/
def beobWert (V : Sichtbar) (r : Register) (s : Zustand) : Option Wort :=
  if V.lebendig r then some (s.register r) else none

/-- Executable memory projection: visible bytes show their value, hidden
    bytes show `none`. -/
def beobByteAt (V : Sichtbar) (a : Adresse) (s : Zustand) : Option Byte :=
  if V.adr a then some (s.speicher.bytes a) else none

/-- A dead register projects to `none` whatever it holds: scratch writes
    are invisible at the projection. -/
theorem beobWert_tot (V : Sichtbar) (r : Register) (s : Zustand)
    (h : V.lebendig r = false) :
    beobWert V r s = none := by
  simp [beobWert, h]

/-- A live register projects to its actual value: contracts hold at actual
    values, never quantified away. -/
theorem beobWert_lebendig (V : Sichtbar) (r : Register) (s : Zustand)
    (h : V.lebendig r = true) :
    beobWert V r s = some (s.register r) := by
  simp [beobWert, h]

/-- Concrete scope: the data cell 8192 is visible, `rbx` is live, everything
    else (including the scratch register `rax`) is hidden. -/
def V0 : Sichtbar :=
  { adr := fun a => decide (a = BitVec.ofNat 64 8192),
    lebendig := fun r => decide (r = Register.rbx) }

/-- Cell 8192 is visible. -/
theorem V0_adr_8192 : V0.adr (BitVec.ofNat 64 8192) = true := by
  decide

/-- `rbx` is live. -/
theorem V0_lebendig_rbx : V0.lebendig Register.rbx = true := by
  decide

/-- `rax` is dead scratch. -/
theorem V0_tot_rax : V0.lebendig Register.rax = false := by
  decide

/-- Witness flags: nothing set. -/
def wFlags : Flags :=
  { cf := false, pf := true, af := some false, zf := false, sf := false,
    of := false }

/-- Witness memory: zeroed bytes, fully readable and writable. -/
def wMem : Speicher :=
  { bytes := fun _ => BitVec.ofNat 8 0, lesbar := fun _ => true,
    schreibbar := fun _ => true, ausfuehrbar := fun _ => false }

/-- Witness memory with one HIDDEN byte set: address 100 holds 1, outside
    the visible scope, so no sound projection may show it. -/
def wMemT : Speicher :=
  { bytes := fun a =>
      if a = BitVec.ofNat 64 100 then BitVec.ofNat 8 1
      else BitVec.ofNat 8 0,
    lesbar := fun _ => true, schreibbar := fun _ => true,
    ausfuehrbar := fun _ => false }

/-- Start register file: stack top at 8192, `rbx` holds 7, `rax` is zero. -/
def wRegS : Register → Wort := fun q =>
  if q = Register.rsp then BitVec.ofNat 64 8192
  else if q = Register.rbx then BitVec.ofNat 64 7
  else BitVec.ofNat 64 0

/-- Twin register file: identical except dead `rax` holds 99. -/
def wRegT : Register → Wort := fun q =>
  if q = Register.rsp then BitVec.ofNat 64 8192
  else if q = Register.rbx then BitVec.ofNat 64 7
  else if q = Register.rax then BitVec.ofNat 64 99
  else BitVec.ofNat 64 0

/-- Witness start state. -/
def wS : Zustand :=
  { register := wRegS, flags := wFlags, rip := BitVec.ofNat 64 4096,
    speicher := wMem }

/-- Twin start state: differs from `wS` only in dead `rax` and in the one
    hidden memory byte. -/
def wT : Zustand :=
  { register := wRegT, flags := wFlags, rip := BitVec.ofNat 64 4096,
    speicher := wMemT }

/-! ## Internal move: a scratch write to a dead register is invisible. -/

/-- A `movImm64` into a DEAD register preserves observation equality across
    the step: RIP advances equally from equal positions, flags and memory
    are untouched by construction, and every live register differs from the
    dead destination. Scratch (`htot`), frame (memory) and liveness (live
    registers) assumptions are all used; none is redundant. -/
theorem movImm64_tot_erhaelt_beob (V : Sichtbar) (d : Decodiert)
    (s t s' t' : Zustand) (dst : Register) (v : Wort)
    (hok : laengeOk d.laenge = true)
    (hbef : d.befehl = .movImm64 dst v)
    (hs : schritt d s = some s')
    (ht : schritt d t = some t')
    (hgleich : BeobGleich V s t)
    (htot : V.lebendig dst = false) :
    BeobGleich V s' t' := by
  rw [schritt_movImm64 d s dst v hok hbef] at hs
  rw [schritt_movImm64 d t dst v hok hbef] at ht
  cases hs
  cases ht
  obtain ⟨hrip, hflags, hmem, hreg⟩ := hgleich
  refine ⟨?_, ?_, ?_, ?_⟩
  · show ripNach s.rip d.laenge = ripNach t.rip d.laenge
    rw [hrip]
  · show (schrittRegister s _ s.flags dst v).flags =
      (schrittRegister t _ t.flags dst v).flags
    simp only [schrittRegister]
    exact hflags
  · intro a ha
    show (schrittRegister s _ s.flags dst v).speicher.bytes a =
      (schrittRegister t _ t.flags dst v).speicher.bytes a
    simp only [schrittRegister]
    exact hmem a ha
  · intro r hr
    have hne : r ≠ dst := by
      intro heq
      rw [heq, htot] at hr
      exact Bool.false_ne_true hr
    show regSet s.register dst v r = regSet t.register dst v r
    rw [regSet_fremd s.register dst r v hne,
      regSet_fremd t.register dst r v hne]
    exact hreg r hr

/-! ## Joint witness: observably equal twins with hidden differences. -/

/-- The twins are observably equal: same control position, same flags, same
    visible byte, same live registers — despite dead `rax` (0 vs 99) and the
    hidden byte at address 100. Every premise is used: the visible address
    hypothesis places `a` at 8192, away from the hidden byte. -/
theorem wS_wT_beobgleich : BeobGleich V0 wS wT := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro a ha
    have he : a = BitVec.ofNat 64 8192 :=
      of_decide_eq_true (by simpa [V0] using ha)
    have hne : a ≠ BitVec.ofNat 64 100 := by
      rw [he]
      decide
    simp only [wS, wT, wMem, wMemT]
    simp [hne]
  · intro r hr
    have he : r = Register.rbx :=
      of_decide_eq_true (by simpa [V0] using hr)
    subst he
    simp [wS, wT, wRegS, wRegT]

/-- JOINT WITNESS for `movImm64_tot_erhaelt_beob`: all premises
    instantiated together — observably equal twins, a real dead-register
    difference, and both successors still observably equal after the scratch
    write. Non-degenerate: the twins differ observably nowhere but differ
    really in dead `rax`. -/
theorem movImm64_tot_erhaelt_beob_zeuge :
    BeobGleich V0 wS wT ∧ wS.register Register.rax ≠ wT.register Register.rax ∧
      BeobGleich V0
        (schrittRegister wS (ripNach wS.rip 3) wS.flags Register.rax 42)
        (schrittRegister wT (ripNach wT.rip 3) wT.flags Register.rax 42) := by
  refine ⟨wS_wT_beobgleich, by decide, ?_⟩
  exact movImm64_tot_erhaelt_beob V0 ⟨.movImm64 Register.rax 42, 3⟩
    wS wT _ _ Register.rax 42 (by decide) rfl
    (schritt_movImm64 _ _ _ _ (by decide) rfl)
    (schritt_movImm64 _ _ _ _ (by decide) rfl)
    wS_wT_beobgleich (by decide)

/-! ## Memory-changing run and negative observable-fault case. -/

/-- MEMORY-CHANGING witnessed run: the accepted MOV/STORE/LOAD chain moves
    42 into live `rbx` and observably changes the visible cell from zero to
    42. The projection shows the change; nothing is hidden here. -/
theorem zeige_beob_speicher_aendert_sich :
    ((lauf zeugeProg zeugeZustand).map
      (fun s => beobByteAt V0 (BitVec.ofNat 64 8192) s) =
      some (some (BitVec.ofNat 8 42))) ∧
    beobByteAt V0 (BitVec.ofNat 64 8192) zeugeZustand =
      some (BitVec.ofNat 8 0) ∧
    ((lauf zeugeProg zeugeZustand).map
      (fun s => beobWert V0 Register.rbx s) =
      some (some (BitVec.ofNat 64 42))) := by
  decide

/-- SCRATCH stays hidden along the same run: dead `rax` holds 42 after the
    first move, yet projects to `none` while live `rbx` shows its value. -/
theorem zeige_kratz_verdeckt :
    ((lauf [⟨.movImm64 Register.rax 42, 3⟩] zeugeZustand).map
      (fun s => beobWert V0 Register.rax s) = some none) ∧
    ((lauf [⟨.movImm64 Register.rax 42, 3⟩] zeugeZustand).map
      (fun s => s.register Register.rax) = some (BitVec.ofNat 64 42)) := by
  decide

/-- NEGATIVE observable-fault case: the executable chain steps (kind
    `true`) while the execute-denied byte refuses (kind `false`). A fault
    never looks like success. -/
theorem zeige_fehler_beobachtbar :
    beobKind (byteschritt ketteStart) = true ∧
      beobKind (byteschritt ohneExecStart) = false := by
  decide

/- CUTS:
    Proved here: the canonical observation projection shape (`Sichtbar`,
    `BeobGleich` with RIP, flags, visible memory and live registers),
    executable snapshots (`beobSchnappschuss`, `beobWert`, `beobByteAt`,
    `beobKind`), the outcome projection (`beobAusgang`, `Beobachtung`) with
    refusal observably distinct from success, and the pilot internal-move
    fact `movImm64_tot_erhaelt_beob` (scratch write to a dead register is
    invisible) with a joint concrete witness, a memory-changing witnessed
    run, a scratch-hidden probe and a negative observable-fault case.
    NOT proved here, and not claimed:
    - No preservation fact for any other pilot form (`movReg64`, ALU,
      load/store, jumps, stack, call/ret): each needs its own scratch,
      frame and liveness argument. `movReg64` additionally needs the source
      register live or equal on both sides.
    - No fault-identity claim: every refusal projects to one coarse
      `fehler`; page fault vs decode fault vs failed access are not
      distinguished, and memory written before a mid-run fault is not part
      of the fault outcome (run-level observation is OPEN).
    - No hidden-channel completeness claim: only dead registers are hidden,
      under the explicit per-point liveness premise the consumer (register
      allocation, dead-code elimination) must establish. Timing,
      microarchitecture, power and concurrent observers are never part of
      the projection; per-byte TSO is not multi-byte atomicity.
    - No source correspondence: no Gabbro source, contract, call log, I/O,
      budget, cost or time claim; source cost/call/I-O/full bridge stays
      OPEN. No concurrency, interrupt, entry, ABI, relocation, image or
      physical-hardware claim.
-/

#print axioms beobAusgang_verweigert
#print axioms beobAusgang_weiter_ungleich
#print axioms beobGleich_refl
#print axioms beobWert_tot
#print axioms beobWert_lebendig
#print axioms V0_adr_8192
#print axioms V0_lebendig_rbx
#print axioms V0_tot_rax
#print axioms movImm64_tot_erhaelt_beob
#print axioms wS_wT_beobgleich
#print axioms movImm64_tot_erhaelt_beob_zeuge
#print axioms zeige_beob_speicher_aendert_sich
#print axioms zeige_kratz_verdeckt
#print axioms zeige_fehler_beobachtbar

end Gabbro.Grammatik.X86
