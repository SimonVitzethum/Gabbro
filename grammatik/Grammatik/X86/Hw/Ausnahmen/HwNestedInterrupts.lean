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
import Grammatik.X86.Hw.Ausnahmen.HwInterrupts
import Grammatik.X86.Hw.Familien.HwStackCalls
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

/-! ## 6. Family adapter and extended step relation.

   The nested family plugs into §11 two ways: single async events
   keep the accepted plug shape, and the extended relation embeds
   `HwSchritt` exactly -- forward and backward. -/

/-- The nested family adapter: a pair of async events delivered as a
    nest under the first event's control snapshot; the machine
    projection is the final machine. -/
def adapterVerschachtelt : HwAdapter (AsyncEreignis × AsyncEreignis) :=
  ⟨fun m c ev =>
    match verschachteltSchritt m c ev.1 ev.2 ev.1.steuer with
    | none => none
    | some (m2, _, _, _) => some m2⟩

/-- The adapter refuses whatever the nest refuses: failed first leg. -/
theorem adapterVerschachtelt_verweigert_erster (m : HwMaschine)
    (c : Nat) (ev : AsyncEreignis × AsyncEreignis)
    (h1 : asyncSchritt m c ev.1 ev.1.steuer = none) :
    adapterVerschachtelt.schritt m c ev = none := by
  have h := verschachtelt_verweigert_erster m c ev.1 ev.2
    ev.1.steuer h1
  simp [adapterVerschachtelt, h]

/-- The adapter refuses whatever the nest refuses: masked second leg
    after an IF-clearing first delivery. -/
theorem adapterVerschachtelt_verweigert_maskiert (m : HwMaschine)
    (c : Nat) (ev : AsyncEreignis × AsyncEreignis)
    (r1 : HwMaschine × Bool × Bool)
    (h1 : asyncSchritt m c ev.1 ev.1.steuer = some r1)
    (hif : r1.2.1 = false)
    (hmatch : ev.2.steuer = { ev.1.steuer with ifBit := r1.2.1 })
    (hart : ev.2.art = .maskierbar)
    (hv : asyncVektorOk ev.2 = true) :
    adapterVerschachtelt.schritt m c ev = none := by
  have h := verschachtelt_maskiert_verweigert m c ev.1 ev.2
    ev.1.steuer r1 h1 hif hmatch hart hv
  simp [adapterVerschachtelt, h]

/-- Every adapter step preserves well-formedness. -/
theorem adapterVerschachtelt_wf (m : HwMaschine) (c : Nat)
    (ev : AsyncEreignis × AsyncEreignis) (m' : HwMaschine)
    (h : adapterVerschachtelt.schritt m c ev = some m')
    (hwf : HwWf m) : HwWf m' := by
  unfold adapterVerschachtelt at h
  cases hn : verschachteltSchritt m c ev.1 ev.2 ev.1.steuer with
  | none => simp [hn] at h
  | some r =>
    obtain ⟨m2, ifNeu2, gew1, gew2⟩ := r
    simp only [hn] at h
    cases h
    exact verschachteltSchritt_wf m c ev.1 ev.2 ev.1.steuer _ hn hwf

/-- Extended events: synchronous machine steps, single async delivery,
    or nested delivery of two events. -/
inductive NestEreignis where
  | syncEv : HwEreignis → NestEreignis
  | asyncEv : AsyncEreignis → NestEreignis
  | nestEv : AsyncEreignis → AsyncEreignis → NestEreignis
  deriving DecidableEq, Repr

/-- Extended step: `HwSchritt` embedded unchanged (control kept),
    single delivery via `asyncSchritt`, nested delivery via the two
    chained legs with the snapshot tracking the first new IF. -/
inductive HwNestSchritt :
    HwIntMaschine → HwIntMaschine → NestEreignis → Prop where
  | sync {s : HwIntMaschine} {m' : HwMaschine} {e : HwEreignis}
      (h : HwSchritt s.hw m' e) :
      HwNestSchritt s ⟨m', s.steuer⟩ (.syncEv e)
  | async {s : HwIntMaschine} (c : Nat) (ev : AsyncEreignis)
      {m' : HwMaschine} {ifNeu : Bool} {gew : Bool}
      (hst : ev.steuer = s.steuer c)
      (h : asyncSchritt s.hw c ev (s.steuer c) = some (m', ifNeu, gew)) :
      HwNestSchritt s ⟨m', fun d =>
        if d = c then { s.steuer c with ifBit := ifNeu }
        else s.steuer d⟩ (.asyncEv ev)
  | nest {s : HwIntMaschine} (c : Nat) (ev1 ev2 : AsyncEreignis)
      {r1 : HwMaschine × Bool × Bool}
      {m2 : HwMaschine} {ifNeu2 : Bool} {gew2 : Bool}
      (hst1 : ev1.steuer = s.steuer c)
      (h1 : asyncSchritt s.hw c ev1 (s.steuer c) = some r1)
      (hst2 : ev2.steuer = { s.steuer c with ifBit := r1.2.1 })
      (h2 : asyncSchritt r1.1 c ev2 { s.steuer c with ifBit := r1.2.1 } =
        some (m2, ifNeu2, gew2)) :
      HwNestSchritt s ⟨m2, fun d =>
        if d = c then { s.steuer c with ifBit := ifNeu2 }
        else s.steuer d⟩ (.nestEv ev1 ev2)

/-- EMBEDDING IN: every coherent step rides along unchanged. -/
theorem hwNestSchritt_sync_einbetten (s : HwIntMaschine)
    (m' : HwMaschine) (e : HwEreignis)
    (h : HwSchritt s.hw m' e) :
    HwNestSchritt s ⟨m', s.steuer⟩ (.syncEv e) :=
  .sync h

/-- EMBEDDING ONLY: a sync-labelled extended step IS a coherent step
    with untouched control. -/
theorem hwNestSchritt_sync_nur (s s' : HwIntMaschine) (e : HwEreignis)
    (h : HwNestSchritt s s' (.syncEv e)) :
    ∃ m', s'.hw = m' ∧ s'.steuer = s.steuer ∧ HwSchritt s.hw m' e := by
  cases h with
  | sync h => exact ⟨_, rfl, rfl, h⟩

/-- Every extended step preserves well-formedness: old steps by the
    accepted preservation, delivery steps because profiles are never
    touched. -/
theorem hwNestSchritt_wf (s s' : HwIntMaschine) (e : NestEreignis)
    (h : HwNestSchritt s s' e) (hwf : HwWf s.hw) : HwWf s'.hw := by
  cases h with
  | sync hstep => exact hwSchritt_wf s.hw _ _ hstep hwf
  | async c ev hst h =>
    exact asyncSchritt_wf_allgemein _ _ _ _ _ h hwf
  | nest c ev1 ev2 hst1 h1 hst2 h2 =>
    exact asyncSchritt_wf_allgemein _ _ _ _ _ h2
      (asyncSchritt_wf_allgemein _ _ _ _ _ h1 hwf)

/-! ## 7. Joint witness: two maskable gates, nested delivery, #DF.

   IDT at 4096 with 34 entries (limit 543): vector 2 is the reused
   NMI interrupt gate (handler `0x2000`), vector 32 a TRAP gate
   (handler `0x2100`, keeps IF) and vector 33 an INTERRUPT gate
   (handler `0x2200`, clears IF). TSS and stack mirror the accepted
   witness (IST1 holds `0x4000`, frame window 16336-16384). Every
   claim below is a closed decidable observation. -/

/-- Witness trap-gate low word (vector 32): offset `0x2100`,
    selector `0x08`, IST 1, `P/DPL/type = 0x8F` (trap). -/
def loWit32Nat : Nat :=
  33 * 256 + 8 * 65536 + 1 * 4294967296 + 143 * 1099511627776

/-- Witness trap-gate low word. -/
def loWit32 : Wort := BitVec.ofNat 64 loWit32Nat

/-- Witness interrupt-gate low word (vector 33): offset `0x2200`,
    selector `0x08`, IST 1, `P/DPL/type = 0x8E` (interrupt). -/
def loWit33Nat : Nat :=
  34 * 256 + 8 * 65536 + 1 * 4294967296 + 142 * 1099511627776

/-- Witness interrupt-gate low word. -/
def loWit33 : Wort := BitVec.ofNat 64 loWit33Nat

/-- IDT image bytes relative to 4096: the vector-2 gate at +32, the
    vector-32 trap gate at +512, the vector-33 interrupt gate at +528. -/
def nestIdtByte (n : Nat) : Byte :=
  match n with
  | 32 => natByte 0
  | 33 => natByte 32
  | 34 => natByte 8
  | 35 => natByte 0
  | 36 => natByte 1
  | 37 => natByte 142
  | 512 => natByte 0
  | 513 => natByte 33
  | 514 => natByte 8
  | 515 => natByte 0
  | 516 => natByte 1
  | 517 => natByte 143
  | 528 => natByte 0
  | 529 => natByte 34
  | 530 => natByte 8
  | 531 => natByte 0
  | 532 => natByte 1
  | 533 => natByte 142
  | _ => BitVec.ofNat 8 0

/-- TSS image bytes relative to 12288: IST1 (`0x4000`) at +36. -/
def nestTssByte (n : Nat) : Byte :=
  match n with
  | 36 => natByte 0
  | 37 => natByte 64
  | _ => BitVec.ofNat 8 0

/-- Witness bytes: IDT and TSS images, zero elsewhere. -/
def nestIntBytes (a : Adresse) : Byte :=
  if a.toNat < 4096 then BitVec.ofNat 8 0
  else if a.toNat < 4096 + 544 then nestIdtByte (a.toNat - 4096)
  else if a.toNat < 12288 then BitVec.ofNat 8 0
  else if a.toNat < 12288 + 48 then nestTssByte (a.toNat - 12288)
  else BitVec.ofNat 8 0

/-- Witness memory: IDT/TSS/stack readable, stack writable. -/
def nestMem : Speicher :=
  { bytes := nestIntBytes
    lesbar := fun a =>
      decide (4096 ≤ a.toNat ∧ a.toNat < 4096 + 544) ||
        decide (12288 ≤ a.toNat ∧ a.toNat < 12288 + 48) ||
        decide (16336 ≤ a.toNat ∧ a.toNat < 16384)
    schreibbar := fun a => decide (16336 ≤ a.toNat ∧ a.toNat < 16384)
    ausfuehrbar := fun _ => false }

/-- Witness control: IDT limit 543, TSS limit 103, CPL 0, IF set. -/
def nestSteuer : Steuerstand :=
  ⟨BitVec.ofNat 64 4096, 543, BitVec.ofNat 64 12288, 103, 0, true⟩

/-- First event: maskable vector 32 (trap gate) under IF set. -/
def evMask32 : AsyncEreignis :=
  ⟨32, .maskierbar, nestSteuer, true, false, 0,
    BitVec.ofNat 64 16, BitVec.ofNat 64 514, BitVec.ofNat 64 8,
    BitVec.ofNat 64 4660, none⟩

/-- Second event: maskable vector 33 (interrupt gate) with the
    post-trap snapshot (IF still set). -/
def evMask33 : AsyncEreignis :=
  ⟨33, .maskierbar, { nestSteuer with ifBit := true }, true, false, 0,
    BitVec.ofNat 64 16, BitVec.ofNat 64 514, BitVec.ofNat 64 8,
    BitVec.ofNat 64 4660, none⟩

/-- Masked probe: maskable vector 32 under cleared IF. -/
def evMaskiert32 : AsyncEreignis :=
  ⟨32, .maskierbar, { nestSteuer with ifBit := false }, true, false, 0,
    BitVec.ofNat 64 16, BitVec.ofNat 64 514, BitVec.ofNat 64 8,
    BitVec.ofNat 64 4660, none⟩

/-- NMI probe: vector 2 under cleared IF (must bypass). -/
def evNmi2 : AsyncEreignis :=
  ⟨2, .nichtMaskierbar, { nestSteuer with ifBit := false }, true,
    false, 0, BitVec.ofNat 64 16, BitVec.ofNat 64 514,
    BitVec.ofNat 64 8, BitVec.ofNat 64 4660, none⟩

/-- Witness cores: core 0 runs with RSP 20480, core 1 idles. -/
def nestKern : Nat → HwKern
  | 0 => ⟨fun q => if q = Register.rsp then BitVec.ofNat 64 20480
      else BitVec.ofNat 64 0,
      zeugeFlags, BitVec.ofNat 64 4096,
      fun _ => BitVec.ofNat 128 0, kontextReset⟩
  | _ => ⟨fun q => if q = Register.rsp then BitVec.ofNat 64 8192
      else BitVec.ofNat 64 0,
      zeugeFlags, BitVec.ofNat 64 8192,
      fun _ => BitVec.ofNat 128 0, kontextReset⟩

/-- Witness start machine: two-gate IDT/TSS/stack memory, empty
    buffers, full silicon. -/
def nestStart : HwMaschine :=
  ⟨nestMem, nestKern, fun _ => [], basisHw, fun _ => basisBereit⟩

/-- Witness control for every core. -/
def nestSteuerAlle : Nat → Steuerstand := fun _ => nestSteuer

/-- The witness machine is well-formed. -/
theorem nestStart_wf : HwWf nestStart := by
  intro c f h
  exact (merkmalZugelassen_heisst_beide nestStart.hw
    (nestStart.bereit c) f h).1

/-- The vector-32 gate bytes read back as the trap words. -/
theorem nestTor32_liest :
    liesTorBytes nestMem (torAdresse (BitVec.ofNat 64 4096) 32) =
      some (loWit32, 0) := by
  decide

/-- The vector-33 gate bytes read back as the interrupt words. -/
theorem nestTor33_liest :
    liesTorBytes nestMem (torAdresse (BitVec.ofNat 64 4096) 33) =
      some (loWit33, 0) := by
  decide

/-- The vector-2 gate bytes read back as the reused NMI words. -/
theorem nestTor2_liest :
    liesTorBytes nestMem (torAdresse (BitVec.ofNat 64 4096) 2) =
      some (loWit, 0) := by
  decide

/-- The trap gate is admitted (handler `0x2100`, trap kind). -/
theorem nestTor32_bereit :
    pruefeTor 32 543 (loWit32, (0 : Wort)) .extern 0 true =
      .bereit ⟨BitVec.ofNat 64 8448, 8, 1, 0, false⟩ := by
  decide

/-- The interrupt gate is admitted (handler `0x2200`). -/
theorem nestTor33_bereit :
    pruefeTor 33 543 (loWit33, (0 : Wort)) .extern 0 true =
      .bereit ⟨BitVec.ofNat 64 8704, 8, 1, 0, true⟩ := by
  decide

/-- The witness TSS slot loads the IST stack. -/
theorem nestStapel :
    waehleStapel nestMem nestSteuer 1 0 false
      (BitVec.ofNat 64 20480) =
      .wechseln (BitVec.ofNat 64 16384) := by
  decide

/-- The selected stack pointer is canonical. -/
theorem nestKanonisch :
    istKanonisch (BitVec.ofNat 64 16384) = true := by
  decide

/-! ## 8. Delivery observations on the witness.

   First the maskable trap delivery (keeps IF), then the nested
   maskable interrupt delivery (clears IF), then the masked refusal
   and the NMI bypass under cleared IF. -/

/-- First delivery: maskable vector 32 on core 0. -/
def nestD1 : Option (HwMaschine × Bool × Bool) :=
  asyncSchritt nestStart 0 evMask32 nestSteuer

/-- Nested delivery: vector 32 then vector 33 on core 0. -/
def nestVerschachtelt : Option (HwMaschine × Bool × Bool × Bool) :=
  verschachteltSchritt nestStart 0 evMask32 evMask33 nestSteuer

/-- Nested projections: handler RIP out of a nested outcome. -/
def nestRipOut (o : Option (HwMaschine × Bool × Bool × Bool))
    (c : Nat) : Option Wort :=
  match o with
  | some (m, _, _, _) => some (m.kerne c).rip
  | _ => none

/-- Nested projections: final IF out of a nested outcome. -/
def nestIfOut (o : Option (HwMaschine × Bool × Bool × Bool)) :
    Option Bool :=
  match o with
  | some (_, b, _, _) => some b
  | _ => none

/-- Nested projections: buffer length out of a nested outcome. -/
def nestBufOut (o : Option (HwMaschine × Bool × Bool × Bool))
    (c : Nat) : Option Nat :=
  match o with
  | some (m, _, _, _) => some (m.puffer c).length
  | _ => none

/-- Nested projections: delivered memory (witness memory on refusal). -/
def nestMemOut (o : Option (HwMaschine × Bool × Bool × Bool)) :
    Speicher :=
  match o with
  | some (m, _, _, _) => m.mem
  | none => nestMem

/-- MASKABLE SUCCESS: delivery reaches the trap handler `0x2100`. -/
theorem nestD1_rip :
    asyncRipOut nestD1 0 = some (BitVec.ofNat 64 8448) := by
  decide

/-- The trap gate keeps IF (S5, witnessed). -/
theorem nestD1_if :
    asyncIfOut nestD1 = some true := by
  decide

/-- Delivery reports the IST switch. -/
theorem nestD1_gew :
    asyncGewOut nestD1 = some true := by
  decide

/-- S3 witnessed: no buffer grew on the acting core. -/
theorem nestD1_puffer_0 : asyncBufOut nestD1 0 = some 0 := by
  decide

/-- S3 witnessed: no buffer grew on the other core either. -/
theorem nestD1_puffer_1 : asyncBufOut nestD1 1 = some 0 := by
  decide

/-- First frame word reads back. -/
theorem nestD1_rahmen_ss :
    read64 (asyncMemOut nestD1) (BitVec.ofNat 64 16376) =
      some (BitVec.ofNat 64 16) := by
  decide

/-- Last frame word reads back. -/
theorem nestD1_rahmen_rip :
    read64 (asyncMemOut nestD1) (BitVec.ofNat 64 16344) =
      some (BitVec.ofNat 64 4660) := by
  decide

/-- NESTED SUCCESS: the second delivery reaches `0x2200`. -/
theorem nestV_rip :
    nestRipOut nestVerschachtelt 0 = some (BitVec.ofNat 64 8704) := by
  decide

/-- The nested interrupt gate clears IF (S5, witnessed). -/
theorem nestV_if :
    nestIfOut nestVerschachtelt = some false := by
  decide

/-- S3 witnessed across the nest: acting buffer still empty. -/
theorem nestV_puffer_0 : nestBufOut nestVerschachtelt 0 = some 0 := by
  decide

/-- S3 witnessed across the nest: other buffer still empty. -/
theorem nestV_puffer_1 : nestBufOut nestVerschachtelt 1 = some 0 := by
  decide

/-- The machine after the nest, if reached. -/
def nestM2 : Option HwMaschine :=
  match nestVerschachtelt with
  | some (m2, _, _, _) => some m2
  | none => none

/-- Third attempt: maskable vector 32 under cleared IF. -/
def nestDritt : Option (HwMaschine × Bool × Bool) :=
  match nestM2 with
  | some m2 =>
    asyncSchritt m2 0 evMaskiert32 { nestSteuer with ifBit := false }
  | none => none

/-- NESTED MASK REFUSES: a maskable event under cleared IF never
    delivers, even with a present gate. -/
theorem nestDritt_verweigert : nestDritt = none := by
  decide

/-- NMI attempt under cleared IF after the nest. -/
def nestNmi : Option (HwMaschine × Bool × Bool) :=
  match nestM2 with
  | some m2 =>
    asyncSchritt m2 0 evNmi2 { nestSteuer with ifBit := false }
  | none => none

/-- NMI BYPASS (S1, witnessed): delivery reaches `0x2000` despite
    cleared IF. -/
theorem nestNmi_rip :
    asyncRipOut nestNmi 0 = some (BitVec.ofNat 64 8192) := by
  decide

/-- The NMI interrupt gate clears IF. -/
theorem nestNmi_if :
    asyncIfOut nestNmi = some false := by
  decide

/-! ## 9. Double-fault observation on the witness.

   First leg delivers through the trap gate; the nested leg names
   vector 35, past the IDT limit, and faults -- escalation to #DF
   (vector 8, code zero). Leg statuses are observed through the
   accepted fault-vector projection. -/

/-- First nested-delivery request (trap gate words, as read). -/
def dfQ1 : LieferAnfrage :=
  ⟨32, (loWit32, BitVec.ofNat 64 0), .extern, true, false, 0,
    BitVec.ofNat 64 20480, BitVec.ofNat 64 16, BitVec.ofNat 64 514,
    BitVec.ofNat 64 8, BitVec.ofNat 64 4660, none⟩

/-- Second nested-delivery request: vector 35, past the IDT limit. -/
def dfQ2 : LieferAnfrage :=
  ⟨35, (loWit32, BitVec.ofNat 64 0), .extern, true, false, 0,
    BitVec.ofNat 64 16344, BitVec.ofNat 64 16, BitVec.ofNat 64 514,
    BitVec.ofNat 64 8, BitVec.ofNat 64 4660, none⟩

/-- First leg delivers (no fault vector). -/
theorem nestDf_h1vektor :
    ergebnisVektor (liefere nestMem nestSteuer dfQ1) = none := by
  decide

/-- Second leg faults with the #GP-class vector. -/
theorem nestDf_h2vektor :
    ergebnisVektor
      (liefere (ergebnisSpeicher (liefere nestMem nestSteuer dfQ1))
        { nestSteuer with ifBit := true } dfQ2) = some 13 := by
  decide

/-- DOUBLE FAULT (S4, witnessed): the escalated outcome carries
    vector 8. -/
theorem nestDf_vektor :
    dfVektorVon (liefereMitDf nestMem nestSteuer dfQ1 dfQ2) =
      some 8 := by
  decide

/-- DOUBLE FAULT (S4, witnessed): the escalated outcome carries
    error code zero. -/
theorem nestDf_code :
    dfCodeVon (liefereMitDf nestMem nestSteuer dfQ1 dfQ2) =
      some 0 := by
  decide

/-! ## 10. TSO stage and buffered frame on the witness.

   Chained onto the first delivery: core 1 issues byte 42 at a cell
   clear of the frame, forwards it to itself only, and the drain
   changes shared memory observed from both cores. Beside it the
   five-word handler frame rides the acting core's buffer (40
   entries, memory unchanged, owner-only word forwarding). -/

/-- Witness data cell: writable, clear of the frame. -/
def nestZelle : Adresse := BitVec.ofNat 64 16336

/-- The machine after the first delivery, if reached. -/
def nestTsoM1 : Option HwMaschine :=
  match nestD1 with
  | some (m1, _, _) => some m1
  | none => none

/-- Core 1 issues byte 42 at the data cell. -/
def nestTso1 : Option TSOZustand :=
  match nestTsoM1 with
  | some m1 => issueByte (tsoAnsicht m1) 1 nestZelle (BitVec.ofNat 8 42)
  | none => none

/-- Core 1 observes its own byte (forwarding). -/
def nestTsoLoadEigen : Option (Option Byte) :=
  match nestTso1 with
  | some s => some (loadByte s 1 nestZelle)
  | none => none

/-- Core 0 observes the old byte (no foreign forwarding). -/
def nestTsoLoadFremd : Option (Option Byte) :=
  match nestTso1 with
  | some s => some (loadByte s 0 nestZelle)
  | none => none

/-- Core 1 drains its oldest entry. -/
def nestTso2 : Option TSOZustand :=
  match nestTso1 with
  | some s => flushKern s 1
  | none => none

/-- The shared byte after the drain. -/
def nestTsoNachFlush : Option (Option Byte) :=
  match nestTso2 with
  | some s => some (some (s.mem.bytes nestZelle))
  | none => none

/-- Core 0 reads the drained byte from shared memory. -/
def nestTsoFremdNachFlush : Option (Option Byte) :=
  match nestTso2 with
  | some s => some (loadByte s 0 nestZelle)
  | none => none

/-- The data cell starts zeroed. -/
theorem nestTso_anfang_null :
    nestMem.bytes nestZelle = BitVec.ofNat 8 0 := by
  decide

/-- Forwarding: core 1 reads its own unflushed byte. -/
theorem nestTso_weiterleitung :
    nestTsoLoadEigen = some (some (BitVec.ofNat 8 42)) := by
  decide

/-- No foreign forwarding: core 0 still reads zero. -/
theorem nestTso_fremd_alt :
    nestTsoLoadFremd = some (some (BitVec.ofNat 8 0)) := by
  decide

/-- The drain changes shared memory: the cell reads 42. -/
theorem nestTso_spuelung_aendert :
    nestTsoNachFlush = some (some (BitVec.ofNat 8 42)) := by
  decide

/-- After the drain core 0 observes the new byte. -/
theorem nestTso_fremd_neu :
    nestTsoFremdNachFlush = some (some (BitVec.ofNat 8 42)) := by
  decide

/-- The five handler frame words (SS, RSP, RFLAGS, CS, RIP). -/
def nestRahmenWorte : List Wort :=
  [BitVec.ofNat 64 16, BitVec.ofNat 64 20480, BitVec.ofNat 64 514,
   BitVec.ofNat 64 8, BitVec.ofNat 64 4660]

/-- The frame buffered on core 0 at the IST top. -/
def nestPuffer : Option HwMaschine :=
  puffereRahmen nestStart 0 (BitVec.ofNat 64 16384) nestRahmenWorte

/-- Buffered entry count on core 0 after the frame push. -/
def nestPufferLen : Option Nat :=
  match nestPuffer with
  | some m => some (m.puffer 0).length
  | none => none

/-- Shared-memory byte at the first slot right after buffering. -/
def nestPufferMemStill : Option Byte :=
  match nestPuffer with
  | some m1 => some (m1.mem.bytes (BitVec.ofNat 64 16376))
  | none => none

/-- Core 0 observes its own buffered first word (forwarding). -/
def nestPufferWortEigen : Option (Option Wort) :=
  match nestPuffer with
  | some m1 =>
    some (stapelLadeWort (tsoAnsicht m1) 0 (BitVec.ofNat 64 16376))
  | none => none

/-- Core 1 observes the old word (no foreign forwarding). -/
def nestPufferWortFremd : Option (Option Wort) :=
  match nestPuffer with
  | some m1 =>
    some (stapelLadeWort (tsoAnsicht m1) 1 (BitVec.ofNat 64 16376))
  | none => none

/-- The buffered frame is exactly 40 entries. -/
theorem nestPuffer_40 : nestPufferLen = some 40 := by
  decide

/-- Buffering leaves the shared slot byte at zero. -/
theorem nestPuffer_mem_still :
    nestPufferMemStill = some (BitVec.ofNat 8 0) := by
  decide

/-- Forwarding: core 0 reads its own unflushed frame word. -/
theorem nestPuffer_wort_eigen :
    nestPufferWortEigen = some (some (BitVec.ofNat 64 16)) := by
  decide

/-- No foreign forwarding: core 1 still reads zero. -/
theorem nestPuffer_wort_fremd :
    nestPufferWortFremd = some (some (BitVec.ofNat 64 0)) := by
  decide

/-! ## 11. IRET observation on the witness.

   After the first delivery the handler returns: RIP and RSP are
   restored from the frame, IF comes back from RFLAGS bit 9. -/

/-- IRET after the first delivery. -/
def nestIret : Option HwIntMaschine :=
  match nestD1 with
  | some (m1, ifNeu, _) =>
    iretSchritt ⟨m1, fun _ => { nestSteuer with ifBit := ifNeu }⟩ 0 true
  | none => none

/-- Restored RIP out of the IRET outcome. -/
def nestIretRip : Option Wort :=
  match nestIret with
  | some s => some (s.hw.kerne 0).rip
  | _ => none

/-- Restored RSP out of the IRET outcome. -/
def nestIretRsp : Option Wort :=
  match nestIret with
  | some s => some ((s.hw.kerne 0).register Register.rsp)
  | _ => none

/-- Restored IF out of the IRET outcome. -/
def nestIretIf : Option Bool :=
  match nestIret with
  | some s => some (s.steuer 0).ifBit
  | _ => none

/-- IRET restores the pre-handler RIP. -/
theorem nestIret_rip :
    nestIretRip = some (BitVec.ofNat 64 4660) := by
  decide

/-- IRET restores the pre-handler RSP. -/
theorem nestIret_rsp :
    nestIretRsp = some (BitVec.ofNat 64 20480) := by
  decide

/-- IRET restores IF from RFLAGS bit 9 (S6, witnessed). -/
theorem nestIret_if :
    nestIretIf = some true := by
  decide

/-! ## 12. Joint witness.

   The first leg succeeds (as an existential triple), the second leg
   succeeds under the tracked IF, and both join the machine-level
   nest equation and the reached extended-relation step. -/

/-- The first leg succeeds. -/
theorem nestH1ex : ∃ r1 : HwMaschine × Bool × Bool,
    asyncSchritt nestStart 0 evMask32 nestSteuer = some r1 := by
  cases he : nestD1 with
  | none =>
    have hrip := nestD1_rip
    simp [he, asyncRipOut] at hrip
  | some r1 => exact ⟨r1, he⟩

/-- JOINT WITNESS: trap delivery (IF kept, IST switch, empty
    buffers, frame read-back), nested interrupt delivery (IF
    cleared), masked refusal, NMI bypass, double-fault escalation
    (vector 8, code zero) with leg statuses, owner-only forwarding
    with a memory-changing drain, the 40-entry buffered frame with
    owner-only word forwarding, IRET restoration, well-formedness,
    the reached machine-level nest and the reached extended step.
    Non-degenerate: two cores touch memory, three deliveries and a
    drain observably change shared-memory bytes. -/
theorem verschachtelt_zeuge :
    asyncRipOut nestD1 0 = some (BitVec.ofNat 64 8448) ∧
      asyncIfOut nestD1 = some true ∧
      asyncGewOut nestD1 = some true ∧
      asyncBufOut nestD1 0 = some 0 ∧
      asyncBufOut nestD1 1 = some 0 ∧
      read64 (asyncMemOut nestD1) (BitVec.ofNat 64 16376) =
        some (BitVec.ofNat 64 16) ∧
      read64 (asyncMemOut nestD1) (BitVec.ofNat 64 16344) =
        some (BitVec.ofNat 64 4660) ∧
      nestRipOut nestVerschachtelt 0 = some (BitVec.ofNat 64 8704) ∧
      nestIfOut nestVerschachtelt = some false ∧
      nestBufOut nestVerschachtelt 0 = some 0 ∧
      nestBufOut nestVerschachtelt 1 = some 0 ∧
      nestDritt = none ∧
      asyncRipOut nestNmi 0 = some (BitVec.ofNat 64 8192) ∧
      asyncIfOut nestNmi = some false ∧
      dfVektorVon (liefereMitDf nestMem nestSteuer dfQ1 dfQ2) =
        some 8 ∧
      dfCodeVon (liefereMitDf nestMem nestSteuer dfQ1 dfQ2) =
        some 0 ∧
      ergebnisVektor (liefere nestMem nestSteuer dfQ1) = none ∧
      ergebnisVektor
          (liefere (ergebnisSpeicher (liefere nestMem nestSteuer dfQ1))
            { nestSteuer with ifBit := true } dfQ2) = some 13 ∧
      nestMem.bytes nestZelle = BitVec.ofNat 8 0 ∧
      nestTsoLoadEigen = some (some (BitVec.ofNat 8 42)) ∧
      nestTsoLoadFremd = some (some (BitVec.ofNat 8 0)) ∧
      nestTsoNachFlush = some (some (BitVec.ofNat 8 42)) ∧
      nestTsoFremdNachFlush = some (some (BitVec.ofNat 8 42)) ∧
      nestPufferLen = some 40 ∧
      nestPufferMemStill = some (BitVec.ofNat 8 0) ∧
      nestPufferWortEigen = some (some (BitVec.ofNat 64 16)) ∧
      nestPufferWortFremd = some (some (BitVec.ofNat 64 0)) ∧
      nestIretRip = some (BitVec.ofNat 64 4660) ∧
      nestIretRsp = some (BitVec.ofNat 64 20480) ∧
      nestIretIf = some true ∧
      HwWf nestStart ∧
      (∃ r1 : HwMaschine × Bool × Bool,
        ∃ r2 : HwMaschine × Bool × Bool,
        verschachteltSchritt nestStart 0 evMask32 evMask33
          nestSteuer =
          some (r2.1, r2.2.1, r1.2.2, r2.2.2)) ∧
      (∃ s' : HwIntMaschine, ∃ e : NestEreignis,
        HwNestSchritt ⟨nestStart, nestSteuerAlle⟩ s' e) := by
  have hstep : (∃ r1 : HwMaschine × Bool × Bool,
        ∃ r2 : HwMaschine × Bool × Bool,
        verschachteltSchritt nestStart 0 evMask32 evMask33
          nestSteuer =
          some (r2.1, r2.2.1, r1.2.2, r2.2.2)) ∧
      (∃ s' : HwIntMaschine, ∃ e : NestEreignis,
        HwNestSchritt ⟨nestStart, nestSteuerAlle⟩ s' e) := by
    obtain ⟨⟨m1, ifNeu1, gew1⟩, h1⟩ := nestH1ex
    have hif1 : ifNeu1 = true := by
      have hn1 : nestD1 = some (m1, ifNeu1, gew1) := h1
      have hif := nestD1_if
      rw [hn1] at hif
      simpa [asyncIfOut] using hif
    have hd : decide (evMask33.steuer =
        { nestSteuer with ifBit := ifNeu1 }) = true := by
      simp [evMask33, hif1]
    have h2ex : ∃ r2 : HwMaschine × Bool × Bool,
        asyncSchritt m1 0 evMask33
          { nestSteuer with ifBit := ifNeu1 } = some r2 := by
      cases he : asyncSchritt m1 0 evMask33
          { nestSteuer with ifBit := ifNeu1 } with
      | none =>
        have hrip := nestV_rip
        simp [nestVerschachtelt, verschachteltSchritt, h1, hd, he,
          nestRipOut] at hrip
      | some r2 => exact ⟨r2, rfl⟩
    obtain ⟨⟨m2, ifNeu2, gew2⟩, h2⟩ := h2ex
    have hmatch : evMask33.steuer =
        { nestSteuer with ifBit := (m1, ifNeu1, gew1).2.1 } := by
      simp [evMask33, hif1]
    refine ⟨⟨_, _, verschachtelt_erfolg nestStart 0 evMask32 evMask33
      nestSteuer _ _ h1 hmatch h2⟩, _, _,
      HwNestSchritt.nest 0 evMask32 evMask33 rfl h1
        (by simp [evMask33, nestSteuerAlle, hif1]) h2⟩
  refine ⟨nestD1_rip, nestD1_if, nestD1_gew, nestD1_puffer_0,
    nestD1_puffer_1, nestD1_rahmen_ss, nestD1_rahmen_rip, nestV_rip,
    nestV_if, nestV_puffer_0, nestV_puffer_1, nestDritt_verweigert,
    nestNmi_rip, nestNmi_if, nestDf_vektor, nestDf_code,
    nestDf_h1vektor, nestDf_h2vektor, nestTso_anfang_null,
    nestTso_weiterleitung, nestTso_fremd_alt, nestTso_spuelung_aendert,
    nestTso_fremd_neu, nestPuffer_40, nestPuffer_mem_still,
    nestPuffer_wort_eigen, nestPuffer_wort_fremd, nestIret_rip,
    nestIret_rsp, nestIret_if, nestStart_wf, hstep.1, hstep.2⟩

/- CUTS:
   Proved here, over the accepted coherent machine (HardwareExecution
   §11: `HwMaschine`/`HwSchritt`/`HwAdapter`/`HwWf`/`HwStern`), the
   accepted descriptor-layer evaluator (`liefere` and its stage
   lemmas), the accepted single delivery (`asyncSchritt`,
   HwInterrupts.lean) and the accepted buffered word effects
   (`hwWortAusgabe`/`issueListe`, HwStackCalls.lean) -- nothing
   redefined, everything lifted:
   - nested delivery (`verschachteltSchritt`: second event under the
     first delivery's new IF, snapshot must track) with refusal of a
     failed first leg, a stale snapshot and a masked second leg
     after an IF-clearing delivery (S1+S5), the success equation,
     general single-delivery wf preservation and nested wf
     preservation (§2);
   - nested wechseln/wechseln agreement with both accepted
     `liefere` legs -- same frame memories, handler RIPs, IF values
     and switch flags, over the descended RSP link (§2);
   - double fault as outcome (`DfErgebnis`/`liefereMitDf`): first
     fault reported, two successes deliver, a nested fault while
     entering the handler escalates to #DF with vector 8 and code
     zero (S4) (§3);
   - the TSO-buffered handler frame (`puffereRahmen` at the same
     descending slots `schiebeRahmen` writes): wf preservation, no
     shared-memory change, eight entries per word, every byte one
     `HwSchritt.gibAus` event, the folded frame as a `HwStern`
     chain, byte echo against `write64` (§4);
   - IRET return (`iretLese`/`iretFertig`/`iretSchritt`): five-word
     pop, RIP/RSP restore, IF from RFLAGS bit 9 (S6), NULL-selector
     and code-row checks, wf preservation, success and all five
     planted refusals (§5);
   - the family adapter (`adapterVerschachtelt`) with wf
     preservation and planted-refusal projection, and the extended
     relation (`HwNestSchritt`) with the EXACT two-way sync
     embedding of `HwSchritt` and wf preservation (§6);
   - joint non-degenerate witness (`verschachtelt_zeuge`): TWO
     maskable gates over byte-populated canonical memory -- trap
     vector 32 delivers (handler `0x2100`, IF kept, IST switch,
     empty buffers, frame read-back), nested interrupt vector 33
     delivers (handler `0x2200`, IF cleared), a masked third
     refuses, NMI vector 2 bypasses cleared IF (handler `0x2000`);
     DF escalation observed (vector 8, code zero) with leg
     statuses (first delivers, nested faults #GP-vector); a
     core-1 buffered store with owner-only forwarding and a drain
     changing shared memory observed from both cores; the five-word
     frame as 40 buffer entries with owner-only word forwarding;
     IRET restoring RIP/RSP/IF; well-formedness; the reached
     machine-level nest and the reached extended-relation step.
   NOT proved here, and not claimed:
   - No hardware correspondence: S1-S6 cite the Intel SDM extracts
     as provenance (MUSE-REPORT-660 catalogue); the proofs show
     self-consistency of the lifted model only.
   - No APIC/priority arbitration, SMI, timing, power or thermal
     paths; no serialising-drain claim beyond S3.
   - No per-access target-to-W/GX simulation and no whole-word
     atomicity beyond the accepted `WortGruppe` guard; the TSO
     stage reuses the accepted byte equations only.
   - DF is witnessed observationally (outcome vector/code
     projections plus both leg fault-vector statuses beside the
     abstract escalation theorem): memory has no `DecidableEq`,
     so no concrete `liefereMitDf_doppelt` application is stated.
   - IRET covers the five-word same-frame return only: no
     privilege-level switch reversal, no error-code pop
     semantics, no segment state beyond the NULL checks (the
     machine has no segment registers).
   - Nested agreement is proved for the wechseln/wechseln stack
     path only; other path combinations follow the same accepted
     lemmas and stay open.
   - No handler EXECUTION: what runs after delivery stays
     downstream (entry lane); no CPL change, no task gates, no
     shadow-stack/CET/FRED paths.
   - `gabbro_ziel` axioms are untouched.
-/

#print axioms dfVektor
#print axioms dfCode
#print axioms verschachteltSchritt
#print axioms verschachtelt_verweigert_erster
#print axioms verschachtelt_verweigert_abbild
#print axioms verschachtelt_erfolg
#print axioms verschachtelt_maskiert_verweigert
#print axioms asyncSchritt_wf_allgemein
#print axioms verschachteltSchritt_wf
#print axioms DfErgebnis
#print axioms dfVektorVon
#print axioms dfCodeVon
#print axioms liefereMitDf
#print axioms liefereMitDf_erste_fehlschlaegt
#print axioms liefereMitDf_doppelt
#print axioms liefereMitDf_zugestellt
#print axioms verschachtelt_vereinbarung
#print axioms puffereRahmen
#print axioms hwWortAusgabe_wf
#print axioms puffereRahmen_wf
#print axioms puffereRahmen_kein_speicher
#print axioms puffereRahmen_zaehlt
#print axioms rahmenByte_ausgabe
#print axioms HwStern_verkettet
#print axioms hwWortAusgabe_stern
#print axioms puffereRahmen_stern
#print axioms rahmenEcho_schreiben
#print axioms iretLese
#print axioms iretIf
#print axioms iretHwNeu
#print axioms iretSteuerNeu
#print axioms iretFertig
#print axioms iretSchritt
#print axioms intWf1181
#print axioms iretSchritt_wf
#print axioms iretSchritt_erfolg
#print axioms iretSchritt_verweigert_lesung
#print axioms iretSchritt_verweigert_nichtkanonisch
#print axioms iretSchritt_verweigert_cs
#print axioms iretSchritt_verweigert_ss
#print axioms iretSchritt_verweigert_code
#print axioms adapterVerschachtelt
#print axioms adapterVerschachtelt_verweigert_erster
#print axioms adapterVerschachtelt_verweigert_maskiert
#print axioms adapterVerschachtelt_wf
#print axioms NestEreignis
#print axioms HwNestSchritt
#print axioms hwNestSchritt_sync_einbetten
#print axioms hwNestSchritt_sync_nur
#print axioms hwNestSchritt_wf
#print axioms nullSelektor
#print axioms nullSelektor_null
#print axioms nullSelektor_acht
#print axioms loWit32
#print axioms loWit33
#print axioms nestIdtByte
#print axioms nestTssByte
#print axioms nestIntBytes
#print axioms nestMem
#print axioms nestSteuer
#print axioms evMask32
#print axioms evMask33
#print axioms evMaskiert32
#print axioms evNmi2
#print axioms nestKern
#print axioms nestStart
#print axioms nestSteuerAlle
#print axioms nestStart_wf
#print axioms nestTor32_liest
#print axioms nestTor33_liest
#print axioms nestTor2_liest
#print axioms nestTor32_bereit
#print axioms nestTor33_bereit
#print axioms nestStapel
#print axioms nestKanonisch
#print axioms nestD1
#print axioms nestVerschachtelt
#print axioms nestRipOut
#print axioms nestIfOut
#print axioms nestBufOut
#print axioms nestMemOut
#print axioms nestD1_rip
#print axioms nestD1_if
#print axioms nestD1_gew
#print axioms nestD1_puffer_0
#print axioms nestD1_puffer_1
#print axioms nestD1_rahmen_ss
#print axioms nestD1_rahmen_rip
#print axioms nestV_rip
#print axioms nestV_if
#print axioms nestV_puffer_0
#print axioms nestV_puffer_1
#print axioms nestM2
#print axioms nestDritt
#print axioms nestDritt_verweigert
#print axioms nestNmi
#print axioms nestNmi_rip
#print axioms nestNmi_if
#print axioms dfQ1
#print axioms dfQ2
#print axioms nestDf_h1vektor
#print axioms nestDf_h2vektor
#print axioms nestDf_vektor
#print axioms nestDf_code
#print axioms nestZelle
#print axioms nestTsoM1
#print axioms nestTso1
#print axioms nestTsoLoadEigen
#print axioms nestTsoLoadFremd
#print axioms nestTso2
#print axioms nestTsoNachFlush
#print axioms nestTsoFremdNachFlush
#print axioms nestTso_anfang_null
#print axioms nestTso_weiterleitung
#print axioms nestTso_fremd_alt
#print axioms nestTso_spuelung_aendert
#print axioms nestTso_fremd_neu
#print axioms nestRahmenWorte
#print axioms nestPuffer
#print axioms nestPufferLen
#print axioms nestPufferMemStill
#print axioms nestPufferWortEigen
#print axioms nestPufferWortFremd
#print axioms nestPuffer_40
#print axioms nestPuffer_mem_still
#print axioms nestPuffer_wort_eigen
#print axioms nestPuffer_wort_fremd
#print axioms nestIret
#print axioms nestIretRip
#print axioms nestIretRsp
#print axioms nestIretIf
#print axioms nestIret_rip
#print axioms nestIret_rsp
#print axioms nestIret_if
#print axioms nestH1ex
#print axioms verschachtelt_zeuge

end Gabbro.Grammatik.X86
