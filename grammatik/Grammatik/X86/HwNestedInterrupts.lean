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

/-! ## 3. Double fault as outcome (S4).

   A fault raised while the handler of a fault is being entered
   escalates: the accepted `liefere` fault of the SECOND delivery
   becomes #DF, vector 8, error code zero. The first delivery's own
   fault is reported unchanged; two successes deliver. -/

/-- Nested outcome with #DF: success, a first-delivery fault, or the
    escalated double fault (vector 8, code zero). -/
inductive DfErgebnis where
  | zugestellt : Speicher → Adresse → Bool → Bool → DfErgebnis
  | fehler : TorFehler → Wort → DfErgebnis
  | doppelFehler : DfErgebnis

/-- Fault vector projection: a first-delivery fault keeps the
    accepted `torVektor`; the double fault is vector 8 (S4). -/
def dfVektorVon : DfErgebnis → Option Nat
  | .zugestellt _ _ _ _ => none
  | .fehler f _ => some (torVektor f)
  | .doppelFehler => some dfVektor

/-- Error-code projection: a first-delivery fault keeps its code;
    the double fault carries zero (S4). -/
def dfCodeVon : DfErgebnis → Option Wort
  | .zugestellt _ _ _ _ => none
  | .fehler _ c => some c
  | .doppelFehler => some dfCode

/-- Nested delivery with escalation: the first `liefere` fault is
    reported, two successes deliver, a second-delivery fault while
    entering the handler escalates to #DF. -/
def liefereMitDf (m : Speicher) (s : Steuerstand)
    (q1 q2 : LieferAnfrage) : DfErgebnis :=
  match liefere m s q1 with
  | .lieferFehler f c => .fehler f c
  | .zugestellt m1 _ ifNeu _ =>
    match liefere m1 { s with ifBit := ifNeu } q2 with
    | .zugestellt m2 rip ifNeu2 gew => .zugestellt m2 rip ifNeu2 gew
    | .lieferFehler _ _ => .doppelFehler

/-- FIRST FAULT REPORTED: a failed first delivery is no escalation. -/
theorem liefereMitDf_erste_fehlschlaegt (m : Speicher)
    (s : Steuerstand) (q1 q2 : LieferAnfrage) (f : TorFehler)
    (c : Wort)
    (h1 : liefere m s q1 = .lieferFehler f c) :
    liefereMitDf m s q1 q2 = .fehler f c := by
  simp [liefereMitDf, h1]

/-- DOUBLE FAULT (S4): the handler was entered and the nested
    delivery faults -- vector 8, error code zero. -/
theorem liefereMitDf_doppelt (m m1 : Speicher) (s : Steuerstand)
    (q1 q2 : LieferAnfrage) (rip : Adresse) (ifNeu : Bool)
    (gew : Bool) (f2 : TorFehler) (c2 : Wort)
    (h1 : liefere m s q1 = .zugestellt m1 rip ifNeu gew)
    (h2 : liefere m1 { s with ifBit := ifNeu } q2 =
      .lieferFehler f2 c2) :
    liefereMitDf m s q1 q2 = .doppelFehler ∧
      dfVektorVon (liefereMitDf m s q1 q2) = some dfVektor ∧
      dfCodeVon (liefereMitDf m s q1 q2) = some dfCode := by
  have h : liefereMitDf m s q1 q2 = .doppelFehler := by
    simp [liefereMitDf, h1, h2]
  refine ⟨h, ?_, ?_⟩ <;> rw [h] <;> rfl

/-- TWO SUCCESSES DELIVER: no fault anywhere, no escalation. -/
theorem liefereMitDf_zugestellt (m m1 m2 : Speicher) (s : Steuerstand)
    (q1 q2 : LieferAnfrage) (rip1 rip2 : Adresse)
    (ifNeu1 ifNeu2 : Bool) (gew1 gew2 : Bool)
    (h1 : liefere m s q1 = .zugestellt m1 rip1 ifNeu1 gew1)
    (h2 : liefere m1 { s with ifBit := ifNeu1 } q2 =
      .zugestellt m2 rip2 ifNeu2 gew2) :
    liefereMitDf m s q1 q2 = .zugestellt m2 rip2 ifNeu2 gew2 := by
  simp [liefereMitDf, h1, h2]

/-- (2) AGREEMENT, nested wechseln/wechseln path: the nest succeeds
    exactly where both accepted `liefere` legs deliver -- same frame
    memories, handler RIPs, IF values and switch flags. The old
    evaluator is lifted, never redefined. Every premise feeds the
    leg that consumes it; the descended RSP links the legs. -/
theorem verschachtelt_vereinbarung (m : HwMaschine) (c : Nat)
    (ev1 ev2 : AsyncEreignis) (st1 : Steuerstand)
    (t1 : Wort × Wort) (g1 : IdtTor)
    (curRsp1w rsp1w : Wort) (m2a : Speicher)
    (hv1 : asyncVektorOk ev1 = true)
    (hb1 : asyncBereit ev1 = true)
    (hl1 : torImLimit st1.idtLimit ev1.vektor = true)
    (hr1 : liesTorBytes m.mem (torAdresse st1.idtBasis ev1.vektor) =
      some t1)
    (hcur1 : (m.kerne c).register Register.rsp = curRsp1w)
    (hp1 : pruefeTor ev1.vektor st1.idtLimit t1 .extern st1.cpl
      ev1.codeOk = .bereit g1)
    (hs1 : waehleStapel m.mem st1 g1.ist ev1.neuDpl ev1.wechsel
      curRsp1w = .wechseln rsp1w)
    (hk1 : istKanonisch rsp1w = true)
    (hpush1 : schiebeRahmen m.mem rsp1w
      (rahmenWorte (asyncAnfrage ev1 t1 curRsp1w)) = some m2a)
    (hmatch : ev2.steuer = { st1 with ifBit :=
      if g1.unterbrechung then false else st1.ifBit })
    (t2 : Wort × Wort) (g2 : IdtTor)
    (rsp2w : Wort) (m2b : Speicher)
    (hv2 : asyncVektorOk ev2 = true)
    (hb2 : asyncBereit ev2 = true)
    (hl2 : torImLimit ({ st1 with ifBit :=
      if g1.unterbrechung then false else st1.ifBit }).idtLimit
      ev2.vektor = true)
    (hr2 : liesTorBytes m2a (torAdresse ({ st1 with ifBit :=
      if g1.unterbrechung then false else st1.ifBit }).idtBasis
      ev2.vektor) = some t2)
    (hcur2 : (((asyncMasch m c g1 (asyncAnfrage ev1 t1 curRsp1w)
      rsp1w m2a).kerne c).register Register.rsp) =
      rsp1w - BitVec.ofNat 64
        (8 * (rahmenWorte (asyncAnfrage ev1 t1 curRsp1w)).length))
    (hp2 : pruefeTor ev2.vektor ({ st1 with ifBit :=
        if g1.unterbrechung then false else st1.ifBit }).idtLimit t2
      .extern ({ st1 with ifBit :=
        if g1.unterbrechung then false else st1.ifBit }).cpl
      ev2.codeOk = .bereit g2)
    (hs2 : waehleStapel m2a ({ st1 with ifBit :=
        if g1.unterbrechung then false else st1.ifBit })
      g2.ist ev2.neuDpl ev2.wechsel (rsp1w - BitVec.ofNat 64
        (8 * (rahmenWorte (asyncAnfrage ev1 t1 curRsp1w)).length)) =
      .wechseln rsp2w)
    (hk2 : istKanonisch rsp2w = true)
    (hpush2 : schiebeRahmen m2a rsp2w
      (rahmenWorte (asyncAnfrage ev2 t2 (rsp1w - BitVec.ofNat 64
        (8 * (rahmenWorte (asyncAnfrage ev1 t1 curRsp1w)).length)))) =
      some m2b) :
    ∃ r2 : HwMaschine × Bool × Bool,
      verschachteltSchritt m c ev1 ev2 st1 =
        some (r2.1, r2.2.1, true, r2.2.2) ∧
      liefere m.mem st1 (asyncAnfrage ev1 t1 curRsp1w) =
        .zugestellt m2a g1.offset
          (if g1.unterbrechung then false else st1.ifBit) true ∧
      liefere m2a { st1 with ifBit :=
          if g1.unterbrechung then false else st1.ifBit }
        (asyncAnfrage ev2 t2 (rsp1w - BitVec.ofNat 64
          (8 * (rahmenWorte (asyncAnfrage ev1 t1 curRsp1w)).length))) =
        .zugestellt m2b g2.offset
          (if g2.unterbrechung then false else
            (if g1.unterbrechung then false else st1.ifBit))
          true := by
  have hz1 := asyncSchritt_zugestellt_wechsel m c ev1 st1 t1 g1
    curRsp1w rsp1w m2a hv1 hb1 hl1 hr1 hcur1 hp1 hs1 hk1 hpush1
  have hz2 := asyncSchritt_zugestellt_wechsel
    (asyncMasch m c g1 (asyncAnfrage ev1 t1 curRsp1w) rsp1w m2a)
    c ev2 { st1 with ifBit :=
      if g1.unterbrechung then false else st1.ifBit }
    t2 g2 (rsp1w - BitVec.ofNat 64
      (8 * (rahmenWorte (asyncAnfrage ev1 t1 curRsp1w)).length))
    rsp2w m2b hv2 hb2 hl2 hr2 hcur2 hp2 hs2 hk2 hpush2
  have hlief1 := asyncSchritt_liefere_wechsel m ev1 st1 t1 g1
    curRsp1w rsp1w m2a hp1 hs1 hk1 hpush1
  have hlief2 := asyncSchritt_liefere_wechsel
    (asyncMasch m c g1 (asyncAnfrage ev1 t1 curRsp1w) rsp1w m2a)
    ev2 { st1 with ifBit :=
      if g1.unterbrechung then false else st1.ifBit }
    t2 g2 (rsp1w - BitVec.ofNat 64
      (8 * (rahmenWorte (asyncAnfrage ev1 t1 curRsp1w)).length))
    rsp2w m2b hp2 hs2 hk2 hpush2
  have hnest : verschachteltSchritt m c ev1 ev2 st1 =
      some (asyncMasch (asyncMasch m c g1 (asyncAnfrage ev1 t1 curRsp1w)
        rsp1w m2a) c g2
        (asyncAnfrage ev2 t2 (rsp1w - BitVec.ofNat 64
          (8 * (rahmenWorte (asyncAnfrage ev1 t1 curRsp1w)).length)))
        rsp2w m2b,
      if g2.unterbrechung then false else
        (if g1.unterbrechung then false else st1.ifBit),
      true, true) :=
    verschachtelt_erfolg m c ev1 ev2 st1
      (asyncMasch m c g1 (asyncAnfrage ev1 t1 curRsp1w) rsp1w m2a,
        if g1.unterbrechung then false else st1.ifBit, true)
      (asyncMasch (asyncMasch m c g1 (asyncAnfrage ev1 t1 curRsp1w)
        rsp1w m2a) c g2
        (asyncAnfrage ev2 t2 (rsp1w - BitVec.ofNat 64
          (8 * (rahmenWorte (asyncAnfrage ev1 t1 curRsp1w)).length)))
        rsp2w m2b,
      if g2.unterbrechung then false else
        (if g1.unterbrechung then false else st1.ifBit),
      true)
      hz1 hmatch hz2
  exact ⟨(asyncMasch (asyncMasch m c g1 (asyncAnfrage ev1 t1 curRsp1w)
    rsp1w m2a) c g2
    (asyncAnfrage ev2 t2 (rsp1w - BitVec.ofNat 64
      (8 * (rahmenWorte (asyncAnfrage ev1 t1 curRsp1w)).length)))
    rsp2w m2b,
  if g2.unterbrechung then false else
    (if g1.unterbrechung then false else st1.ifBit),
  true), hnest, hlief1, hlief2⟩

/-! ## 4. Handler entry through the TSO store buffer.

   The accepted `schiebeRahmen` frame lands via `write64`; the same
   words ride the acting core's TSO buffer here as eight
   `wortEintraege` bytes each at the SAME descending slots
   (`HwStackCalls.lean` discipline: buffered issue, owner-only
   forwarding, drain into shared memory). Every buffered byte IS one
   `HwSchritt.gibAus` event; the folded frame is a `HwStern` chain. -/

/-- Buffered frame push: the words as `hwWortAusgabe` folds at the
    same descending slots `schiebeRahmen` writes. `none` = at least
    one slot byte refused. -/
def puffereRahmen (m : HwMaschine) (c : Nat) (top : Adresse) :
    List Wort → Option HwMaschine
  | [] => some m
  | w :: rest =>
    match hwWortAusgabe m c (top - BitVec.ofNat 64 8) w with
    | none => none
    | some m1 => puffereRahmen m1 c (top - BitVec.ofNat 64 8) rest

/-- A buffered word issue preserves well-formedness. -/
theorem hwWortAusgabe_wf (m : HwMaschine) (c : Nat) (a : Adresse)
    (v : Wort) (m' : HwMaschine)
    (h : hwWortAusgabe m c a v = some m')
    (hwf : HwWf m) : HwWf m' := by
  unfold hwWortAusgabe at h
  cases h1 : issueListe (tsoAnsicht m) c (wortEintraege a v) with
  | none => rw [h1] at h; cases h
  | some s' =>
    rw [h1] at h
    cases h
    exact setTso_wf _ s' hwf

/-- A buffered frame preserves well-formedness. -/
theorem puffereRahmen_wf (m : HwMaschine) (c : Nat) (top : Adresse)
    (l : List Wort) (m' : HwMaschine)
    (h : puffereRahmen m c top l = some m')
    (hwf : HwWf m) : HwWf m' := by
  induction l generalizing m top m' with
  | nil =>
    simp [puffereRahmen] at h
    cases h
    exact hwf
  | cons w rest ih =>
    unfold puffereRahmen at h
    cases h1 : hwWortAusgabe m c (top - BitVec.ofNat 64 8) w with
    | none => rw [h1] at h; cases h
    | some m1 =>
      rw [h1] at h
      exact ih m1 _ _ h (hwWortAusgabe_wf m c _ w m1 h1 hwf)

/-- A buffered frame changes no shared-memory byte. -/
theorem puffereRahmen_kein_speicher (m : HwMaschine) (c : Nat)
    (top : Adresse) (l : List Wort) (m' : HwMaschine)
    (h : puffereRahmen m c top l = some m') (x : Adresse) :
    m'.mem.bytes x = m.mem.bytes x := by
  induction l generalizing m top m' with
  | nil =>
    simp [puffereRahmen] at h
    cases h
    rfl
  | cons w rest ih =>
    unfold puffereRahmen at h
    cases h1 : hwWortAusgabe m c (top - BitVec.ofNat 64 8) w with
    | none => rw [h1] at h; cases h
    | some m1 =>
      rw [h1] at h
      rw [ih m1 _ _ h]
      exact hwWortAusgabe_kein_speicher m c _ w m1 h1 x

/-- A buffered frame appends exactly eight entries per word on the
    acting core. -/
theorem puffereRahmen_zaehlt (m : HwMaschine) (c : Nat)
    (top : Adresse) (l : List Wort) (m' : HwMaschine)
    (h : puffereRahmen m c top l = some m') :
    (m'.puffer c).length = (m.puffer c).length + 8 * l.length := by
  induction l generalizing m top m' with
  | nil =>
    simp [puffereRahmen] at h
    cases h
    simp
  | cons w rest ih =>
    unfold puffereRahmen at h
    cases h1 : hwWortAusgabe m c (top - BitVec.ofNat 64 8) w with
    | none => rw [h1] at h; cases h
    | some m1 =>
      rw [h1] at h
      have hp := hwWortAusgabe_puffer m c (top - BitVec.ofNat 64 8) w
        m1 h1
      have ihh := ih m1 _ _ h
      have hlen : (wortEintraege (top - BitVec.ofNat 64 8) w).length
          = 8 := rfl
      rw [ihh, hp, List.length_append, hlen, List.length_cons]
      omega

/-- BYTE ECHO: every buffered frame byte IS a machine store-issue
    event -- the family rides `HwSchritt`, never beside it. -/
theorem rahmenByte_ausgabe (m : HwMaschine) (c : Nat) (a : Adresse)
    (b : Byte) (s' : TSOZustand)
    (h : issueByte (tsoAnsicht m) c a b = some s') :
    HwSchritt m (setTso m s') (.schreibAusgabe c a b) :=
  .gibAus c a b s' h

/-- Transitivity of the machine-step closure. -/
theorem HwStern_verkettet : HwStern m m1 → HwStern m1 m2 → HwStern m m2
  | .refl _, h2 => h2
  | .step _ b _ e hs hr, h2 =>
    .step _ b _ e hs (HwStern_verkettet hr h2)

/-- A buffered word reaches the machine in eight store-issue
    steps (the accepted fold, lifted). -/
theorem hwWortAusgabe_stern (m : HwMaschine) (c : Nat) (a : Adresse)
    (v : Wort) (m' : HwMaschine)
    (h : hwWortAusgabe m c a v = some m') : HwStern m m' := by
  unfold hwWortAusgabe at h
  cases h1 : issueListe (tsoAnsicht m) c (wortEintraege a v) with
  | none => rw [h1] at h; cases h
  | some s' =>
    rw [h1] at h
    cases h
    have hs := issueListe_stern m c (wortEintraege a v)
      (tsoAnsicht m) s' h1
    have hrefl : setTso m (tsoAnsicht m) = m := by
      cases m with
      | mk mem kerne puffer hw bereit => rfl
    rw [hrefl] at hs
    exact hs

/-- A buffered frame reaches the machine as a chain of store-issue
    steps. -/
theorem puffereRahmen_stern (m : HwMaschine) (c : Nat)
    (top : Adresse) (l : List Wort) (m' : HwMaschine)
    (h : puffereRahmen m c top l = some m') :
    HwStern m m' := by
  induction l generalizing m top m' with
  | nil =>
    simp [puffereRahmen] at h
    cases h
    exact .refl _
  | cons w rest ih =>
    unfold puffereRahmen at h
    cases h1 : hwWortAusgabe m c (top - BitVec.ofNat 64 8) w with
    | none => rw [h1] at h; cases h
    | some m1 =>
      rw [h1] at h
      exact HwStern_verkettet
        (hwWortAusgabe_stern m c _ w m1 h1) (ih m1 _ _ h)

/-- The pushed entry carries its `write64` footprint byte: the
    buffered frame and the accepted store agree byte for byte. -/
theorem rahmenEcho_schreiben (m : Speicher) (a : Adresse) (v : Wort)
    (k : Nat) (hk : k < 8) :
    writeBytes m a v (addrOff a k) = wortByte v k :=
  stapelEcho_schreiben m a v k hk

/-! ## 5. IRET return (S6).

   The five-word frame is read back upward from the handler stack
   top (RIP, CS, RFLAGS, old RSP, old SS); RIP is installed, RSP is
   restored, IF comes from RFLAGS bit 9, and the NULL-selector and
   code-row checks refuse loudly. Segment state beyond the checks
   has no machine field (see CUTS). -/

/-- IRET frame read: five words upward from the handler stack top. -/
def iretLese (m : Speicher) (top : Adresse) :
    Option (Wort × Wort × Wort × Wort × Wort) :=
  match read64 m top, read64 m (addrOff top 8),
    read64 m (addrOff top 16), read64 m (addrOff top 24),
    read64 m (addrOff top 32) with
  | some rip, some cs, some fl, some rsp, some ss =>
    some (rip, cs, fl, rsp, ss)
  | _, _, _, _, _ => none

/-- IF restored from RFLAGS bit 9 (S6). -/
def iretIf (fl : Wort) : Bool := decide (fl.toNat / 512 % 2 = 1)

/-- IRET core update: RIP installed, RSP restored, flags/XMM/FP
    kept -- via the accepted `setKernDaten`. -/
def iretHwNeu (s : HwIntMaschine) (c : Nat) (rip rsp : Wort) :
    HwMaschine :=
  setKernDaten s.hw c { s.hw.kerne c with
    register := fun q =>
      if q = Register.rsp then rsp else (s.hw.kerne c).register q,
    rip := rip }

/-- IRET control update: IF from RFLAGS bit 9 on the acting core. -/
def iretSteuerNeu (s : HwIntMaschine) (c : Nat) (fl : Wort) :
    Nat → Steuerstand :=
  fun d => if d = c then { s.steuer c with ifBit := iretIf fl }
  else s.steuer d

/-- NULL-selector check: the word is the zero selector. Kept
    folded in proofs (like `istKanonisch`): branch on its value,
    never on the underlying byte equality. -/
def nullSelektor (w : Wort) : Bool := w == 0

/-- A zero word fails the check. -/
theorem nullSelektor_null : nullSelektor 0 = true := rfl

/-- A nonzero witness word passes the check. -/
theorem nullSelektor_acht : nullSelektor 8 = false := rfl

/-- IRET finish stage over the popped words (mirrors `asyncFertig`):
    canonical-pointer check first, then the selector and code-row
    checks. The first failure refuses with `none`. -/
def iretFertig (s : HwIntMaschine) (c : Nat) (rip cs fl rsp ss : Wort)
    (codeOk : Bool) : Option HwIntMaschine :=
  if !istKanonisch rip then none
  else if nullSelektor cs then none
  else if nullSelektor ss then none
  else if !codeOk then none
  else some ⟨iretHwNeu s c rip rsp, iretSteuerNeu s c fl⟩

/-- IRET step on the extended machine: five-word pop, then
    `iretFertig`. A failed read or check refuses with `none` and
    changes nothing. -/
def iretSchritt (s : HwIntMaschine) (c : Nat) (codeOk : Bool) :
    Option HwIntMaschine :=
  match iretLese s.hw.mem ((s.hw.kerne c).register Register.rsp) with
  | none => none
  | some (rip, cs, fl, rsp, ss) =>
    iretFertig s c rip cs fl rsp ss codeOk

/-- Extended well-formedness: the coherent machine is well-formed. -/
def intWf1181 (s : HwIntMaschine) : Prop := HwWf s.hw

/-- IRET preserves extended well-formedness (profiles untouched). -/
theorem iretSchritt_wf (s : HwIntMaschine) (c : Nat) (codeOk : Bool)
    (s' : HwIntMaschine)
    (h : iretSchritt s c codeOk = some s')
    (hwf : intWf1181 s) : intWf1181 s' := by
  unfold iretSchritt iretFertig at h
  cases hles : iretLese s.hw.mem ((s.hw.kerne c).register Register.rsp) with
  | none => simp [hles] at h
  | some p =>
    obtain ⟨rip, cs, fl, rsp, ss⟩ := p
    cases hkan : istKanonisch rip with
    | false => simp [hles, hkan] at h
    | true =>
      cases hcs : nullSelektor cs with
      | true => simp [hles, hkan, hcs] at h
      | false =>
        cases hss : nullSelektor ss with
        | true => simp [hles, hkan, hcs, hss] at h
        | false =>
          cases hok : codeOk with
          | false => simp [hles, hkan, hcs, hss, hok] at h
          | true =>
            simp [hles, hkan, hcs, hss, hok] at h
            cases h
            show HwWf (iretHwNeu s c rip rsp)
            unfold iretHwNeu
            exact setKernDaten_wf s.hw c _ hwf

/-- SUCCESS: the frame pops, RIP/RSP/IF are restored. -/
theorem iretSchritt_erfolg (s : HwIntMaschine) (c : Nat)
    (codeOk : Bool) (rip cs fl rsp ss : Wort)
    (hles : iretLese s.hw.mem ((s.hw.kerne c).register Register.rsp) =
      some (rip, cs, fl, rsp, ss))
    (hkan : istKanonisch rip = true)
    (hcs : nullSelektor cs = false) (hss : nullSelektor ss = false)
    (hok : codeOk = true) :
    iretSchritt s c codeOk =
      some ⟨iretHwNeu s c rip rsp, iretSteuerNeu s c fl⟩ := by
  unfold iretSchritt iretFertig
  simp [hles, hkan, hcs, hss, hok]

/-- A failed frame read refuses the return. -/
theorem iretSchritt_verweigert_lesung (s : HwIntMaschine) (c : Nat)
    (codeOk : Bool)
    (h : iretLese s.hw.mem ((s.hw.kerne c).register Register.rsp) =
      none) :
    iretSchritt s c codeOk = none := by
  unfold iretSchritt iretFertig
  simp [h]

/-- A noncanonical frame RIP refuses the return. -/
theorem iretSchritt_verweigert_nichtkanonisch (s : HwIntMaschine)
    (c : Nat) (codeOk : Bool) (rip cs fl rsp ss : Wort)
    (hles : iretLese s.hw.mem ((s.hw.kerne c).register Register.rsp) =
      some (rip, cs, fl, rsp, ss))
    (hkan : istKanonisch rip = false) :
    iretSchritt s c codeOk = none := by
  unfold iretSchritt iretFertig
  simp [hles, hkan]

/-- A NULL code selector refuses the return. -/
theorem iretSchritt_verweigert_cs (s : HwIntMaschine)
    (c : Nat) (codeOk : Bool) (rip cs fl rsp ss : Wort)
    (hles : iretLese s.hw.mem ((s.hw.kerne c).register Register.rsp) =
      some (rip, cs, fl, rsp, ss))
    (hkan : istKanonisch rip = true)
    (hcs : nullSelektor cs = true) :
    iretSchritt s c codeOk = none := by
  unfold iretSchritt iretFertig
  simp [hles, hkan, hcs]

/-- A NULL stack selector refuses the return. -/
theorem iretSchritt_verweigert_ss (s : HwIntMaschine)
    (c : Nat) (codeOk : Bool) (rip cs fl rsp ss : Wort)
    (hles : iretLese s.hw.mem ((s.hw.kerne c).register Register.rsp) =
      some (rip, cs, fl, rsp, ss))
    (hkan : istKanonisch rip = true)
    (hcs : nullSelektor cs = false)
    (hss : nullSelektor ss = true) :
    iretSchritt s c codeOk = none := by
  unfold iretSchritt iretFertig
  simp [hles, hkan, hcs, hss]

/-- A failed code-row check refuses the return. -/
theorem iretSchritt_verweigert_code (s : HwIntMaschine)
    (c : Nat) (codeOk : Bool) (rip cs fl rsp ss : Wort)
    (hles : iretLese s.hw.mem ((s.hw.kerne c).register Register.rsp) =
      some (rip, cs, fl, rsp, ss))
    (hkan : istKanonisch rip = true)
    (hcs : nullSelektor cs = false) (hss : nullSelektor ss = false)
    (hok : codeOk = false) :
    iretSchritt s c codeOk = none := by
  unfold iretSchritt iretFertig
  simp [hles, hkan, hcs, hss, hok]

/- CUTS:
   Proved here: SKELETON ONLY so far -- the double-fault vector
   constant. Nested delivery, #DF escalation, the TSO-buffered
   handler frame, IRET and the two-gate maskable witness are OPEN.
   NOT proved here, and not claimed: everything in the lane task.
-/

#print axioms dfVektor

end Gabbro.Grammatik.X86
