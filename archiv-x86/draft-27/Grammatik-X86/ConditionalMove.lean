/-
  File:      Grammatik/X86/ConditionalMove.lean
  Subject:   Reserve register-only conditional-select facts over the accepted
             pilot vocabulary, reusing lane 338 (`ControlFlow.lean`).

  Lane 417 (reserve): no new machine, no new instruction, no codec row and
  no source claim. `ControlFlow.lean` already defines `cmovAnwenden`,
  `cmovSchritt` and the fault-keeping `cmovMemSchritt`; this module proves
  only the missing complementary facts those definitions still need: the
  untaken equation, non-destination preservation, step framing (RIP, flags,
  memory), the bad-length refusal, a safe optional-lowering admission
  (decoded length plus no flag clobber between compare and select), and a
  real pilot-store consumer of the selected value. The memory form keeps
  its fault on the untaken path by the reused `cmovMem_feheler_bleibt`.
-/
import Grammatik.X86.ControlFlow

namespace Gabbro.Grammatik.X86

/-- Safe optional-lowering admission for a register-only conditional
    select: the decoded length is checked data and the flags the select
    reads are exactly the flags the compare produced (no clobber in
    between). Register-only by construction: the reused `cmovAnwenden`
    takes no memory operand. This `Bool` is validator admission, never
    a hardware fault. -/
def cmovLowerOk (d : Decodiert) (flagsNachCmp flagsVorCmov : Flags) : Bool :=
  laengeOk d.laenge && decide (flagsNachCmp = flagsVorCmov)

/-! ## 1. Pure register-only select: taken, untaken, untouched others.

    Complements `ControlFlow.cmovSchritt_genommen` (taken step only):
    the untaken value equation plus preservation of every register
    except the destination. Every premise is used. -/

/-- Untaken select: the destination keeps its pre-state word. -/
theorem cmovAnwenden_nicht_wert (s : Zustand) (dst src : Register)
    (c : Bedingung) (hbed : bedingung c s.flags = false) :
    (cmovAnwenden s dst src c).register dst = s.register dst := by
  unfold cmovAnwenden
  simp [hbed]

/-- Taken select: the destination takes the pre-state source word. -/
theorem cmovAnwenden_genommen_wert (s : Zustand) (dst src : Register)
    (c : Bedingung) (hbed : bedingung c s.flags = true) :
    (cmovAnwenden s dst src c).register dst = s.register src := by
  unfold cmovAnwenden
  simp [hbed]

/-- Every register except the destination keeps its value. -/
theorem cmovAnwenden_fremd (s : Zustand) (dst src q : Register)
    (c : Bedingung) (hq : q ≠ dst) :
    (cmovAnwenden s dst src c).register q = s.register q := by
  simp [cmovAnwenden, hq]

/-! ## 2. Decoded-length step: untaken equation, refusal, framing.

    `ControlFlow` proves only the taken step; the untaken equation, the
    bad-length refusal and the per-step RIP/flags/memory framing are new
    here. Every premise is used. -/

/-- Untaken step: RIP advances past the decoded instruction and the
    destination keeps its pre-state word. -/
theorem cmovSchritt_nicht_genommen (d : Decodiert) (s : Zustand)
    (dst src : Register) (c : Bedingung)
    (hok : laengeOk d.laenge = true)
    (hbed : bedingung c s.flags = false) :
    cmovSchritt d s dst src c =
      some ({ cmovAnwenden s dst src c with rip := ripNach s.rip d.laenge }) ∧
    (cmovAnwenden s dst src c).register dst = s.register dst := by
  refine ⟨?_, cmovAnwenden_nicht_wert s dst src c hbed⟩
  unfold cmovSchritt
  rw [hok]

/-- Bad-length refusal: a failed length check refuses the step. -/
theorem cmovSchritt_verweigert (d : Decodiert) (s : Zustand)
    (dst src : Register) (c : Bedingung)
    (hbad : laengeOk d.laenge = false) :
    cmovSchritt d s dst src c = none := by
  unfold cmovSchritt
  rw [hbad]

/-- A successful select step preserves flags. -/
theorem cmovSchritt_flags (d : Decodiert) (s s' : Zustand)
    (dst src : Register) (c : Bedingung)
    (hok : laengeOk d.laenge = true)
    (hstep : cmovSchritt d s dst src c = some s') :
    s'.flags = s.flags := by
  unfold cmovSchritt at hstep
  rw [hok] at hstep
  cases hstep
  rfl

/-- A successful select step changes no memory byte. -/
theorem cmovSchritt_speicher (d : Decodiert) (s s' : Zustand)
    (dst src : Register) (c : Bedingung)
    (hok : laengeOk d.laenge = true)
    (hstep : cmovSchritt d s dst src c = some s') :
    s'.speicher = s.speicher := by
  unfold cmovSchritt at hstep
  rw [hok] at hstep
  cases hstep
  rfl

/-- A successful select step lands on the post-decode address. -/
theorem cmovSchritt_rip (d : Decodiert) (s s' : Zustand)
    (dst src : Register) (c : Bedingung)
    (hok : laengeOk d.laenge = true)
    (hstep : cmovSchritt d s dst src c = some s') :
    s'.rip = ripNach s.rip d.laenge := by
  unfold cmovSchritt at hstep
  rw [hok] at hstep
  cases hstep
  rfl

/-! ## 3. Safe optional-lowering admission.

    An admitted lowering carries checked decoded length and flag identity
    between the compare and the select (no clobber in between). The
    guarantee below is validator admission, never a hardware fault. -/

/-- ADMISSION GUARANTEE: an admitted lowering has a good decoded length
    and reads exactly the flags the compare produced. -/
theorem cmovLowerOk_garantiert (d : Decodiert)
    (flagsNachCmp flagsVorCmov : Flags)
    (h : cmovLowerOk d flagsNachCmp flagsVorCmov = true) :
    laengeOk d.laenge = true ∧ flagsNachCmp = flagsVorCmov := by
  unfold cmovLowerOk at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hl, hf⟩ := h
  exact ⟨hl, of_decide_eq_true hf⟩

/-- LENGTH REFUSAL: length 0 is no valid decoding, so no lowering. -/
theorem cmovLowerOk_laenge_verweigert :
    cmovLowerOk ⟨.movReg64 .rax .rbx, 0⟩ witTrue.flags witTrue.flags = false := by
  decide

/-- FLAG-CLOBBER REFUSAL: flags changed between compare and select. -/
theorem cmovLowerOk_flags_verweigert :
    cmovLowerOk ⟨.movReg64 .rax .rbx, 3⟩ witTrue.flags witFalse.flags = false := by
  decide

/-- ACCEPTED ADMISSION: good length and identical flags lower. -/
theorem cmovLowerOk_akzeptiert :
    cmovLowerOk ⟨.movReg64 .rax .rbx, 3⟩ witTrue.flags witTrue.flags = true := by
  decide

/-! ## 4. Real pilot-store consumer.

    The taken select value is consumed by the CANONICAL pilot `schritt`
    store (`store64`): after the select, a decoded store of the
    destination register takes exactly the pre-state source word into
    memory. There is no `cmov` constructor in `Befehl` (pilot subset),
    so the select itself stays an optional extension while its value
    flows through real pilot execution. Every premise is used: `hbed`
    rewrites the selected word, `hne` keeps the store address, `h`
    and `hok` drive the reused store equation, `hwr` is the checked
    write. -/

/-- The taken select value reaches pilot memory through a real store. -/
theorem cmov_store_verbraucher (dSt : Decodiert) (s : Zustand)
    (dst src base : Register) (c : Bedingung) (disp : BitVec 32)
    (m : Speicher)
    (hbed : bedingung c s.flags = true)
    (hne : base ≠ dst)
    (h : dSt.befehl = .store64 base dst disp)
    (hok : laengeOk dSt.laenge = true)
    (hwr : write64 s.speicher (effAddr s base disp) (s.register src) = some m) :
    schritt dSt (cmovAnwenden s dst src c) =
      some ({ cmovAnwenden s dst src c with
        speicher := m, rip := ripNach (cmovAnwenden s dst src c).rip dSt.laenge }) ∧
    (cmovAnwenden s dst src c).register dst = s.register src := by
  have hsel := cmovAnwenden_genommen_wert s dst src c hbed
  have hbase : (cmovAnwenden s dst src c).register base = s.register base :=
    cmovAnwenden_fremd s dst src base c hne
  have heff : effAddr (cmovAnwenden s dst src c) base disp = effAddr s base disp := by
    unfold effAddr
    rw [hbase]
  have hmem : (cmovAnwenden s dst src c).speicher = s.speicher :=
    cmovAnwenden_speicher s dst src c
  have hwr' : write64 (cmovAnwenden s dst src c).speicher
      (effAddr (cmovAnwenden s dst src c) base disp)
      ((cmovAnwenden s dst src c).register dst) = some m := by
    rw [hmem, heff, hsel]
    exact hwr
  exact ⟨schritt_store64_erfolg dSt (cmovAnwenden s dst src c) base dst disp m
    hok h hwr', hsel⟩

/-! ## 5. Joint witnesses: concrete premises plus a memory-changing run.

    Each witness instantiates ALL premises on the reused non-degenerate
    states (`witTrue`/`witFalse`: `rax` = 10, `rbx` = 20, stack at 8192)
    and pairs the conclusion with the reused memory-changing run
    `cmov_speicher_zeuge` (selected word 20 stored at 8192, observably
    changing the byte from zero). Taken/untaken value split is reused
    from `cmov_witness_unterscheidet`, not restated. -/

/-- JOINT witness for `cmovSchritt_nicht_genommen`. -/
theorem cmovSchritt_nicht_genommen_zeuge :
    (cmovSchritt ⟨.movReg64 .rax .rbx, 3⟩ witFalse .rax .rbx .e =
      some ({ cmovAnwenden witFalse .rax .rbx .e with
        rip := ripNach witFalse.rip 3 })) ∧
    (cmovAnwenden witFalse .rax .rbx .e).register .rax =
      witFalse.register .rax ∧
    ∃ (m' : Speicher),
      write64 witSpeicher (BitVec.ofNat 64 8192)
        ((cmovAnwenden witTrue .rax .rbx .e).register .rax) = some m' ∧
      read64 m' (BitVec.ofNat 64 8192) = some 20 ∧
      m'.bytes (BitVec.ofNat 64 8192) ≠ witSpeicher.bytes (BitVec.ofNat 64 8192) := by
  have hok : laengeOk 3 = true := by decide
  have hbed : bedingung .e witFalse.flags = false := by decide
  obtain ⟨hstep, hsel⟩ := cmovSchritt_nicht_genommen
    ⟨.movReg64 .rax .rbx, 3⟩ witFalse .rax .rbx .e hok hbed
  exact ⟨hstep, hsel, cmov_speicher_zeuge⟩

/-- JOINT witness for `cmovSchritt_verweigert`: length 0 refuses. -/
theorem cmovSchritt_verweigert_zeuge :
    cmovSchritt ⟨.movReg64 .rax .rbx, 0⟩ witTrue .rax .rbx .e = none ∧
    ∃ (m' : Speicher),
      write64 witSpeicher (BitVec.ofNat 64 8192)
        ((cmovAnwenden witTrue .rax .rbx .e).register .rax) = some m' ∧
      read64 m' (BitVec.ofNat 64 8192) = some 20 ∧
      m'.bytes (BitVec.ofNat 64 8192) ≠ witSpeicher.bytes (BitVec.ofNat 64 8192) := by
  have hbad : laengeOk 0 = false := by decide
  exact ⟨cmovSchritt_verweigert _ _ _ _ _ hbad, cmov_speicher_zeuge⟩

/-- JOINT witness for `cmovLowerOk_garantiert`: accepted admission. -/
theorem cmovLowerOk_garantiert_zeuge :
    (laengeOk 3 = true ∧ witTrue.flags = witTrue.flags) ∧
    ∃ (m' : Speicher),
      write64 witSpeicher (BitVec.ofNat 64 8192)
        ((cmovAnwenden witTrue .rax .rbx .e).register .rax) = some m' ∧
      read64 m' (BitVec.ofNat 64 8192) = some 20 ∧
      m'.bytes (BitVec.ofNat 64 8192) ≠ witSpeicher.bytes (BitVec.ofNat 64 8192) := by
  exact ⟨cmovLowerOk_garantiert _ _ _ cmovLowerOk_akzeptiert,
    cmov_speicher_zeuge⟩

/-- JOINT witness for `cmov_store_verbraucher`: the taken select value
    reaches pilot memory through a real `store64` step and reads back. -/
theorem cmov_store_verbraucher_zeuge :
    ∃ (m : Speicher) (s2 : Zustand),
      schritt ⟨.store64 .rsp .rax (BitVec.ofNat 32 0), 3⟩
        (cmovAnwenden witTrue .rax .rbx .e) = some s2 ∧
      s2.speicher = m ∧
      read64 m (BitVec.ofNat 64 8192) = some 20 ∧
      m.bytes (BitVec.ofNat 64 8192) ≠ witSpeicher.bytes (BitVec.ofNat 64 8192) := by
  have hbed : bedingung .e witTrue.flags = true := by decide
  have hne : Register.rsp ≠ Register.rax := by decide
  have hok : laengeOk 3 = true := by decide
  have heff : effAddr witTrue .rsp (BitVec.ofNat 32 0) = BitVec.ofNat 64 8192 := by
    decide
  have hsrc : witTrue.register .rbx = BitVec.ofNat 64 20 := by decide
  have hsel : (cmovAnwenden witTrue .rax .rbx .e).register .rax = 20 :=
    cmov_witness_unterscheidet.1
  obtain ⟨m, hwr, hread, hdiff⟩ := cmov_speicher_zeuge
  rw [hsel] at hwr
  have hwr2 : write64 witTrue.speicher (effAddr witTrue .rsp (BitVec.ofNat 32 0))
      (witTrue.register .rbx) = some m := by
    rw [heff, hsrc]
    exact hwr
  obtain ⟨hstep, _⟩ := cmov_store_verbraucher
    ⟨.store64 .rsp .rax (BitVec.ofNat 32 0), 3⟩ witTrue .rax .rbx .rsp .e
    (BitVec.ofNat 32 0) m hbed hne rfl hok hwr2
  exact ⟨m, _, hstep, rfl, hread, hdiff⟩

/- CUTS:
   Proved here (all over the REUSED `ControlFlow.cmovAnwenden`,
   `cmovSchritt`, `cmovMemSchritt` and the reused witnesses/states --
   no new machine, no new instruction, no new decoder row):
   - pure select value equations (taken keeps source word, untaken keeps
     destination word) plus preservation of every other register;
     flags/memory framing of the pure application is reused
     (`cmovAnwenden_flags`, `cmovAnwenden_speicher`), not restated;
   - decoded-length select step: untaken equation (taken is reused from
     `cmovSchritt_genommen`), bad-length refusal, and per-step
     RIP/flags/memory framing;
   - safe optional-lowering admission `cmovLowerOk` (checked decoded
     length plus flag identity between compare and select) with the
     start-or-entry style guarantee, one accepted admission and two
     concrete refusals (bad length, flag clobber);
   - real pilot execution consumer: the taken select value is stored by
     the CANONICAL `schritt` store64, with a joint witness whose stored
     word reads back and observably changes memory;
   - joint non-degenerate witnesses (concrete premises plus a
     memory-changing run) for every main theorem; taken/untaken value
     split reused from `cmov_witness_unterscheidet`.
   NOT proved here, and not claimed:
   - No `Befehl` constructor, no `Codec` row, no bytes: CMOVcc has no
     native pilot encoding (`EMITTER-INVENTAR`: NO setcc/cmovcc), so
     there is no codec/source correspondence and no emitted native ISA
     expansion; lengths come from decoded `Decodiert.laenge` only.
   - No hardware correspondence: flag readings reuse `bedingung`,
     faults are the existing permission-checked `read64`/`write64`
     outcomes (the memory form keeps its fault on the untaken path by
     the reused `cmovMem_feheler_bleibt`), not silicon.
   - No full-hardware, TSO/GX, concurrency, source, cost, time or
     termination claim; no timing/speed claim; absence of a transition
     is never a termination statement.
-/

#print axioms cmovAnwenden_nicht_wert
#print axioms cmovAnwenden_genommen_wert
#print axioms cmovAnwenden_fremd
#print axioms cmovSchritt_nicht_genommen
#print axioms cmovSchritt_verweigert
#print axioms cmovSchritt_flags
#print axioms cmovSchritt_speicher
#print axioms cmovSchritt_rip
#print axioms cmovLowerOk_garantiert
#print axioms cmovLowerOk_laenge_verweigert
#print axioms cmovLowerOk_flags_verweigert
#print axioms cmovLowerOk_akzeptiert
#print axioms cmov_store_verbraucher
#print axioms cmovSchritt_nicht_genommen_zeuge
#print axioms cmovSchritt_verweigert_zeuge
#print axioms cmovLowerOk_garantiert_zeuge
#print axioms cmov_store_verbraucher_zeuge

end Gabbro.Grammatik.X86
