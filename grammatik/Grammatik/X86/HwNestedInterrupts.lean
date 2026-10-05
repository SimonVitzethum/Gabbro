/-
  File:      Grammatik/X86/HwNestedInterrupts.lean
  Subject:   Nested interrupt delivery, double fault and handler entry
             on the coherent multicore machine.

  Lane 1181: follow-up of lane 1125 (`HwInterrupts.lean`), whose CUTS
  list no nested delivery, no #DF, no handler execution and no concrete
  maskable-success witness. Lifts the accepted `asyncSchritt`/`liefere`
  delivery (HwInterrupts.lean, InterruptDescriptorHardware.lean) and the
  accepted buffered word effects (`hwWortAusgabe`, HwStackCalls.lean)
  unchanged. Delivery never drains the per-core TSO store buffer; every
  silicon fact beyond self-consistency is named in the ANNAHMEN block
  in §1 and the CUTS block at the end.
-/
import Grammatik.X86.HwInterrupts
import Grammatik.X86.HwStackCalls

namespace Gabbro.Grammatik.X86

/-! ## 1. Silicon assumptions (ANNAHMEN).

   Checked against the clone-local Intel SDM extracts (provenance,
   never proofs; see MUSE-REPORT-660 for the extract catalogue):
   - S1: maskable external interrupts (INTR) are gated by IF; NMI
     bypasses IF (Vol. 3 interrupt delivery; Table 6-1). Reused from
     lane 1125 (`asyncBereit`); nested delivery re-checks the UPDATED
     IF after the first delivery.
   - S2: NMI arrives on vector 2; maskable external vectors are
     32-255 (Table 6-1). Reused from lane 1125 (`asyncVektorOk`).
   - S3: delivery is NOT a serialising drain of the per-core store
     buffer. Reused from lane 1125 (`asyncMasch_puffer_still`).
   - S4: a fault during delivery of a fault escalates to double
     fault #DF, vector 8, error code zero (Table 6-1; Vol. 3A Ch. 7
     `DOUBLE FAULT` exception class).
   - S5: an interrupt gate clears IF on delivery, a trap gate keeps
     it. Reused from lane 1125 (`asyncSchritt_interrupt_loescht_if`,
     `asyncSchritt_trap_behaelt_if`).
   - S6: IRET pops RIP, CS, RFLAGS (and SS:RSP where the frame holds
     them) and restores IF from RFLAGS bit 9; a failed load or a
     noncanonical target faults with #SS/#GP instead of returning.
-/

/-- Double-fault vector (S4): #DF is vector 8. -/
def dfVektor : Nat := 8

/-- #DF carries error code zero (S4). -/
def dfCode : Wort := BitVec.ofNat 64 0

/-! ## 2. Nested delivery: the second event under updated control.

   The second event runs on the successor of the first, under the
   UPDATED control (the first delivery's new IF). Its snapshot must
   track the update (`decide` check); the first failure refuses with
   `none`. Buffers are never drained: both legs are `asyncSchritt`
   legs, each buffer-silent by `asyncMasch_puffer_still`. -/

/-- Nested delivery on core `c`: first `ev1` under `st1`, then `ev2`
    under the first delivery's new IF. Result: the final machine,
    the final IF and both switch flags. -/
def verschachteltSchritt (m : HwMaschine) (c : Nat)
    (ev1 ev2 : AsyncEreignis) (st1 : Steuerstand) :
    Option (HwMaschine × Bool × Bool × Bool) :=
  match asyncSchritt m c ev1 st1 with
  | none => none
  | some r1 =>
    if decide (ev2.steuer = { st1 with ifBit := r1.2.1 }) then
      match asyncSchritt r1.1 c ev2 { st1 with ifBit := r1.2.1 } with
      | none => none
      | some r2 => some (r2.1, r2.2.1, r1.2.2, r2.2.2)
    else none

/-- A refused first delivery refuses the nest. -/
theorem verschachtelt_verweigert_erster (m : HwMaschine) (c : Nat)
    (ev1 ev2 : AsyncEreignis) (st1 : Steuerstand)
    (h1 : asyncSchritt m c ev1 st1 = none) :
    verschachteltSchritt m c ev1 ev2 st1 = none := by
  simp only [verschachteltSchritt, h1]

/-- A stale second snapshot refuses the nest: the snapshot must track
    the first delivery's new IF. -/
theorem verschachtelt_verweigert_abbild (m : HwMaschine) (c : Nat)
    (ev1 ev2 : AsyncEreignis) (st1 : Steuerstand)
    (r1 : HwMaschine × Bool × Bool)
    (h1 : asyncSchritt m c ev1 st1 = some r1)
    (hmis : ¬ ev2.steuer = { st1 with ifBit := r1.2.1 }) :
    verschachteltSchritt m c ev1 ev2 st1 = none := by
  have hd : decide (ev2.steuer = { st1 with ifBit := r1.2.1 }) = false :=
    decide_eq_false_iff_not.mpr hmis
  simp [verschachteltSchritt, h1, hd]

/-- SUCCESS: both legs deliver with a tracking snapshot. -/
theorem verschachtelt_erfolg (m : HwMaschine) (c : Nat)
    (ev1 ev2 : AsyncEreignis) (st1 : Steuerstand)
    (r1 : HwMaschine × Bool × Bool) (r2 : HwMaschine × Bool × Bool)
    (h1 : asyncSchritt m c ev1 st1 = some r1)
    (hmatch : ev2.steuer = { st1 with ifBit := r1.2.1 })
    (h2 : asyncSchritt r1.1 c ev2 { st1 with ifBit := r1.2.1 } =
      some r2) :
    verschachteltSchritt m c ev1 ev2 st1 =
      some (r2.1, r2.2.1, r1.2.2, r2.2.2) := by
  have hd : decide (ev2.steuer = { st1 with ifBit := r1.2.1 }) = true := by
    simp [hmatch]
  simp [verschachteltSchritt, h1, hd, h2]

/-- NESTED MASK REFUSES (S1+S5): the first delivery cleared IF
    through an interrupt gate, so the tracking snapshot has IF clear
    and the maskable second event fails the gate. -/
theorem verschachtelt_maskiert_verweigert (m : HwMaschine) (c : Nat)
    (ev1 ev2 : AsyncEreignis) (st1 : Steuerstand)
    (r1 : HwMaschine × Bool × Bool)
    (h1 : asyncSchritt m c ev1 st1 = some r1)
    (hif : r1.2.1 = false)
    (hmatch : ev2.steuer = { st1 with ifBit := r1.2.1 })
    (hart : ev2.art = .maskierbar)
    (hv : asyncVektorOk ev2 = true) :
    verschachteltSchritt m c ev1 ev2 st1 = none := by
  have hd : decide (ev2.steuer = { st1 with ifBit := r1.2.1 }) = true := by
    simp [hmatch]
  have hb : asyncBereit ev2 = false := by
    simp [asyncBereit, hart, hmatch, hif]
  have h2 := asyncSchritt_verweigert_maskiert r1.1 c ev2
    { st1 with ifBit := r1.2.1 } hv hb
  simp [verschachteltSchritt, h1, hd, h2]

/-- EVERY successful single delivery preserves `HwWf`: case split
    over the accepted stage order, both success leaves by the
    accepted `liefere`-style preservation lemmas. -/
theorem asyncSchritt_wf_allgemein (m : HwMaschine) (c : Nat)
    (ev : AsyncEreignis) (st : Steuerstand)
    (r : HwMaschine × Bool × Bool)
    (h : asyncSchritt m c ev st = some r)
    (hwf : HwWf m) : HwWf r.1 := by
  unfold asyncSchritt at h
  cases hv : asyncVektorOk ev with
  | false => simp [hv] at h
  | true =>
    cases hb : asyncBereit ev with
    | false => simp [hv, hb] at h
    | true =>
      cases hl : torImLimit st.idtLimit ev.vektor with
      | false => simp [hv, hb, hl] at h
      | true =>
        cases hr : liesTorBytes m.mem (torAdresse st.idtBasis ev.vektor) with
        | none => simp [hv, hb, hl, hr] at h
        | some t =>
          cases hp : pruefeTor ev.vektor st.idtLimit t .extern st.cpl
              ev.codeOk with
          | fehler f => simp [hv, hb, hl, hr, hp] at h
          | bereit g =>
            cases hs : waehleStapel m.mem st g.ist ev.neuDpl ev.wechsel
                ((m.kerne c).register Register.rsp) with
            | stapelFehler f => simp [hv, hb, hl, hr, hp, hs] at h
            | behalten rsp =>
              have hcur : (m.kerne c).register Register.rsp =
                (m.kerne c).register Register.rsp := rfl
              cases hk : istKanonisch rsp with
              | false =>
                unfold asyncFertig at h
                simp [hv, hb, hl, hr, hp, hs, hk] at h
              | true =>
                cases hpush : schiebeRahmen m.mem rsp
                    (rahmenWorte (asyncAnfrage ev t
                      ((m.kerne c).register Register.rsp))) with
                | none =>
                  unfold asyncFertig at h
                  simp [hv, hb, hl, hr, hp, hs, hk, hpush] at h
                | some m2 =>
                  exact asyncSchritt_zugestellt_behalten_wf m c ev st t g
                    ((m.kerne c).register Register.rsp) rsp m2
                    hv hb hl hr hcur hp hs hk hpush hwf r h
            | wechseln rsp =>
              have hcur : (m.kerne c).register Register.rsp =
                (m.kerne c).register Register.rsp := rfl
              cases hk : istKanonisch rsp with
              | false =>
                unfold asyncFertig at h
                simp [hv, hb, hl, hr, hp, hs, hk] at h
              | true =>
                cases hpush : schiebeRahmen m.mem rsp
                    (rahmenWorte (asyncAnfrage ev t
                      ((m.kerne c).register Register.rsp))) with
                | none =>
                  unfold asyncFertig at h
                  simp [hv, hb, hl, hr, hp, hs, hk, hpush] at h
                | some m2 =>
                  exact asyncSchritt_zugestellt_wechsel_wf m c ev st t g
                    ((m.kerne c).register Register.rsp) rsp m2
                    hv hb hl hr hcur hp hs hk hpush hwf r h

/-- (1) WELL-FORMEDNESS: every successful nest preserves `HwWf`
    (both legs keep profiles untouched). -/
theorem verschachteltSchritt_wf (m : HwMaschine) (c : Nat)
    (ev1 ev2 : AsyncEreignis) (st1 : Steuerstand)
    (r : HwMaschine × Bool × Bool × Bool)
    (h : verschachteltSchritt m c ev1 ev2 st1 = some r)
    (hwf : HwWf m) : HwWf r.1 := by
  have h1 : ∃ r1, asyncSchritt m c ev1 st1 = some r1 := by
    cases he : asyncSchritt m c ev1 st1 with
    | none =>
      have hnone := verschachtelt_verweigert_erster m c ev1 ev2 st1 he
      rw [hnone] at h
      cases h
    | some r1 => exact ⟨r1, rfl⟩
  obtain ⟨r1, h1⟩ := h1
  have hwf1 : HwWf r1.1 :=
    asyncSchritt_wf_allgemein m c ev1 st1 r1 h1 hwf
  have hd : decide (ev2.steuer = { st1 with ifBit := r1.2.1 }) = true := by
    cases hdm : decide (ev2.steuer = { st1 with ifBit := r1.2.1 }) with
    | false =>
      have hnone := verschachtelt_verweigert_abbild m c ev1 ev2 st1 r1 h1
        (decide_eq_false_iff_not.mp hdm)
      rw [hnone] at h
      cases h
    | true => rfl
  have h2 : ∃ r2, asyncSchritt r1.1 c ev2 { st1 with ifBit := r1.2.1 } =
      some r2 := by
    cases he : asyncSchritt r1.1 c ev2 { st1 with ifBit := r1.2.1 } with
    | none =>
      simp only [verschachteltSchritt, h1, hd, he] at h
      cases h
    | some r2 => exact ⟨r2, rfl⟩
  obtain ⟨r2, h2⟩ := h2
  have hz := verschachtelt_erfolg m c ev1 ev2 st1 r1 r2 h1
    (of_decide_eq_true hd) h2
  rw [hz] at h
  cases h
  exact asyncSchritt_wf_allgemein r1.1 c ev2
    { st1 with ifBit := r1.2.1 } r2 h2 hwf1

/- CUTS:
   Proved here: SKELETON ONLY so far -- the double-fault vector
   constant. Nested delivery, #DF escalation, the TSO-buffered
   handler frame, IRET and the two-gate maskable witness are OPEN.
   NOT proved here, and not claimed: everything in the lane task.
-/

#print axioms dfVektor

end Gabbro.Grammatik.X86
