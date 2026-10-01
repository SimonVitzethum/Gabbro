/-
  File:      Grammatik/X86/ReleaseAcquire.lean
  Subject:   Source/target acquire-release obligations over accepted models.

  Lane 422 (continuous direct-compiler pool): generic acquire-release facts
  reusing the ACTUAL accepted definitions on both sides -- the source view
  primitives `Ordnung`/`beitrag`/`nachricht` of `Speichermodell.Sicht` and
  the target TSO operations `issueByte`/`loadByte`/`flushKern`/`zaunBereit`
  of `X86.TSO`. Target order facts are LOCAL (own buffer, own fence
  readiness); no foreign-buffer drain is claimed. `seq_cst` stays modelled
  as release/acquire (sound over-approximation, no total order claimed).
  No source lowering, no W/GX simulation, no hardware timing.
-/
import Grammatik.X86.TSO
import Grammatik.Speichermodell.Sicht

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik.Speichermodell

/-- Target-side release store: a plain aligned byte issue with NO fence.
    On TSO a release store needs no fence; visibility needs a drain. -/
def ReleaseSchreiben (s s' : TSOZustand) (c : Nat) (a : Adresse)
    (v : Byte) : Prop :=
  issueByte s c a v = some s'

/-! ## 1. Source side: what an acquire read inherits, what a release writes.

    Over the ACTUAL `Ordnung`/`beitrag`/`nachricht` of `Sicht.lean`
    (`freigabe` covers release stores, acquire loads and `seq_cst`;
    `entspannt` is relaxed and every plain access). -/

/-- An acquire read inherits the WHOLE message view, not just its own
    timestamp: the reader joins the writer's released view. -/
theorem freigabe_beitrag_deckt_sicht {Ort : Type} [DecidableEq Ort]
    (x : Ort) (Wert : Type) (m : Nachricht Ort Wert) (y : Ort) :
    m.sicht y ≤ beitrag Ordnung.freigabe x m y := by
  unfold beitrag Sicht.verein
  exact Nat.le_max_left _ _

/-- A release write carries the writer's view at every OTHER location:
    the message publishes exactly what the writer knew. -/
theorem freigabe_nachricht_traegt_sicht {Ort : Type} [DecidableEq Ort]
    (Wert : Type) (v : Sicht Ort) (x : Ort) (ts : Nat) (w : Wert)
    (y : Ort) (h : y ≠ x) :
    (nachricht Ordnung.freigabe v x ts w).sicht y = v y := by
  unfold nachricht
  exact Sicht.setze_anders v ts h

/-- ... and at its own location the message carries its timestamp. -/
theorem freigabe_nachricht_eigen {Ort : Type} [DecidableEq Ort]
    (Wert : Type) (v : Sicht Ort) (x : Ort) (ts : Nat) (w : Wert) :
    (nachricht Ordnung.freigabe v x ts w).sicht x = ts := by
  unfold nachricht
  exact Sicht.setze_selbst v x ts

/-- A relaxed read carries NO foreign view: off its own location the
    contribution is empty. This is the negative half of acquire. -/
theorem entspannt_beitrag_fremd_leer {Ort : Type} [DecidableEq Ort]
    (x : Ort) (Wert : Type) (m : Nachricht Ort Wert) (y : Ort)
    (h : y ≠ x) :
    beitrag Ordnung.entspannt x m y = 0 := by
  unfold beitrag Sicht.eins
  simp [h]

/-- Acquire transfer: after a thread with view `vr` reads message `m` in
    `freigabe` order, its joined view covers the writer's whole view.
    Both premises (reader view, message) pin the conclusion. -/
theorem freigabe_liest_uebertraegt {Ort : Type} [DecidableEq Ort]
    (Wert : Type) (vr : Sicht Ort) (x : Ort) (m : Nachricht Ort Wert)
    (y : Ort) :
    m.sicht y ≤ (vr.verein (beitrag Ordnung.freigabe x m)) y := by
  exact Nat.le_trans (freigabe_beitrag_deckt_sicht x Wert m y)
    (Sicht.verein_rechts _ _ y)

/-! ## 2. Target side: local release/acquire order over TSO.

    Over the ACTUAL `issueByte`/`loadByte`/`flushKern`/`zaunBereit` of
    `TSO.lean`. Every fact is LOCAL to the acting core's buffer; a local
    fence never drains a foreign buffer (`zaun_kein_fremd_drain` there). -/

/-- An empty own buffer means the load reads canonical memory: no
    forwarding applies anywhere. -/
theorem leer_liest_kanonisch (s : TSOZustand) (c : Nat) (a : Adresse)
    (hempty : s.puffer c = [])
    (hrd : s.mem.lesbar a = true) :
    loadByte s c a = some (s.mem.bytes a) := by
  have hmiss : neuestens (s.puffer c) a = none := by
    rw [hempty]
    rfl
  exact load_ohne_eintrag s c a hmiss hrd

/-- A fence-ready acquire load observes canonical memory: once the own
    buffer is drained, no stale forwarded value can surface. -/
theorem zaun_erwerb_liest_kanonisch (s : TSOZustand) (c : Nat)
    (a : Adresse)
    (hzaun : zaunBereit s c = true)
    (hrd : s.mem.lesbar a = true) :
    loadByte s c a = some (s.mem.bytes a) := by
  have hempty : s.puffer c = [] := (zaunBereit_iff_leer s c).mp hzaun
  exact leer_liest_kanonisch s c a hempty hrd

/-- A release store is INVISIBLE to other cores until its buffer entry
    flushes: a foreign core with no pending entry for the address still
    loads the old canonical byte. No fence on the writer changes this;
    only a drain does. Every premise is used: the issue step, the core
    separation, the foreign miss and the permission. -/
theorem freigabe_braucht_flush (s s' : TSOZustand) (c d : Nat)
    (a : Adresse) (v : Byte)
    (h : issueByte s c a v = some s')
    (hne : d ≠ c)
    (hmiss : neuestens (s.puffer d) a = none)
    (hrd : s.mem.lesbar a = true) :
    loadByte s' d a = some (s.mem.bytes a) := by
  have hbuf : s'.puffer d = s.puffer d :=
    issue_anderer_kern s s' c a v h hne
  have hmem : s'.mem.bytes a = s.mem.bytes a :=
    issue_kein_speicher s s' c a v h a
  have hperm := (issue_erhaelt_berechtigungen s s' c a v h).1
  have hmiss' : neuestens (s'.puffer d) a = none := by
    rw [hbuf]
    exact hmiss
  have hrd' : s'.mem.lesbar a = true := by
    rw [hperm]
    exact hrd
  have hload := load_ohne_eintrag s' d a hmiss' hrd'
  rw [hmem] at hload
  exact hload

/-- A release store becomes visible through its OWN drain: issuing from
    an empty buffer and flushing once installs the byte in canonical
    memory. The positive half of the release obligation. -/
theorem freigabe_flush_sichtbar (s s1 s2 : TSOZustand) (c : Nat)
    (a : Adresse) (v : Byte)
    (hempty : s.puffer c = [])
    (h1 : issueByte s c a v = some s1)
    (h2 : flushKern s1 c = some s2) :
    s2.mem.bytes a = v := by
  have hang : s1.puffer c = s.puffer c ++ [⟨a, v⟩] :=
    issue_haengt_an s s1 c a v h1
  rw [hempty] at hang
  simp only [List.nil_append] at hang
  exact flush_schreibt_kopf s1 s2 c h2 ⟨a, v⟩ [] hang

/-- Two release stores drain IN ORDER: after issuing both from an empty
    buffer and flushing twice, the second address holds its value. This
    is the local half of the message-passing shape (data before flag);
    the foreign-visibility half stays with the bridge. -/
theorem fifo_zweite_flush (s s1 s2 s3 s4 : TSOZustand) (c : Nat)
    (a b : Adresse) (v w : Byte)
    (hempty : s.puffer c = [])
    (h1 : issueByte s c a v = some s1)
    (h2 : issueByte s1 c b w = some s2)
    (h3 : flushKern s2 c = some s3)
    (h4 : flushKern s3 c = some s4) :
    s4.mem.bytes b = w := by
  have e1 := issue_haengt_an s s1 c a v h1
  have e2 := issue_haengt_an s1 s2 c b w h2
  rw [hempty] at e1
  simp only [List.nil_append] at e1
  rw [e1] at e2
  have hdrop := flush_entfernt_kopf s2 s3 c h3 ⟨a, v⟩ [⟨b, w⟩] e2
  exact flush_schreibt_kopf s3 s4 c h4 ⟨b, w⟩ [] hdrop

/-- A release store needs NO fence for own-thread visibility: the
    issuing core loads its own value back with no intervening fence.
    Both premises pin it: the release step and the permission. -/
theorem release_braucht_keinen_zaun (s s' : TSOZustand) (c : Nat)
    (a : Adresse) (v : Byte)
    (hrel : ReleaseSchreiben s s' c a v)
    (hrd : s.mem.lesbar a = true) :
    loadByte s' c a = some v :=
  load_nach_issue s s' c a v hrel hrd

/-! ## 3. Stated non-claim: `seq_cst` has no total order here.

    `seq_cst` is modelled as release/acquire (a sound over-approximation
    per DIRECT-COMPILER-DESIGN.md); no total order over all accesses is
    claimed or proved. -/

/-- No total SC order for `seq_cst`-as-release/acquire: the type of such
    a claim is empty. -/
inductive SeqCstTotal : Prop

/-- Every total-order claim is void inside this module. -/
theorem kein_seqcst_total : ¬ SeqCstTotal := by
  intro h
  cases h

/-! ## 4. Joint witnesses: concrete, non-degenerate, memory-changing. -/

/-- Joint witness for `freigabe_braucht_flush`: core 0 release-stores at
    `sbX` from the empty start; core 1, with no pending entry, still loads
    the old canonical byte; flushing core 0 observably changes memory.
    All premises of the theorem hold together on this run. -/
theorem freigabe_braucht_flush_zeuge :
    ∃ s' s'' : TSOZustand,
      issueByte sbStart 0 sbX sbEins = some s' ∧
      loadByte s' 1 sbX = some (sbStart.mem.bytes sbX) ∧
      flushKern s' 0 = some s'' ∧
      s'.mem.bytes sbX ≠ s''.mem.bytes sbX := by
  have hang : sbNach1.puffer 0 = [⟨sbX, sbEins⟩] := by
    decide
  have hfl : ∃ s'', flushKern sbNach1 0 = some s'' := by
    unfold flushKern
    rw [hang]
    exact ⟨_, rfl⟩
  obtain ⟨sfl, hfl⟩ := hfl
  refine ⟨sbNach1, sfl, sb_schritt1, by decide, hfl, ?_⟩
  have hwr := flush_schreibt_kopf sbNach1 sfl 0 hfl ⟨sbX, sbEins⟩ [] hang
  rw [hwr]
  decide

/-- Joint witness for `zaun_erwerb_liest_kanonisch` and
    `freigabe_flush_sichtbar`: the empty start is fence-ready on core 0
    and loads canonical memory; issuing and draining installs the byte,
    so the release became visible through its own drain. -/
theorem freigabe_sichtbar_zeuge :
    zaunBereit sbStart 0 = true ∧
    loadByte sbStart 0 sbX = some (sbStart.mem.bytes sbX) ∧
    ∃ s1 s2 : TSOZustand,
      issueByte sbStart 0 sbX sbEins = some s1 ∧
      flushKern s1 0 = some s2 ∧ s2.mem.bytes sbX = sbEins ∧
      sbStart.mem.bytes sbX ≠ s2.mem.bytes sbX := by
  have hang : sbNach1.puffer 0 = [⟨sbX, sbEins⟩] := by
    decide
  have hfl : ∃ s2, flushKern sbNach1 0 = some s2 := by
    unfold flushKern
    rw [hang]
    exact ⟨_, rfl⟩
  obtain ⟨sfl, hfl⟩ := hfl
  refine ⟨by decide, by decide, sbNach1, sfl, sb_schritt1, hfl, ?_, ?_⟩
  · exact flush_schreibt_kopf sbNach1 sfl 0 hfl ⟨sbX, sbEins⟩ [] hang
  · have hwr := flush_schreibt_kopf sbNach1 sfl 0 hfl ⟨sbX, sbEins⟩ [] hang
    rw [hwr]
    decide

/-- Joint source witness: a concrete message whose view knows location
    1 at timestamp 2. An acquire read of location 0 inherits that full
    view, while a relaxed read of the same message contributes nothing
    off its own location. -/
theorem freigabe_entspannt_zeuge :
    ∃ m : Nachricht Nat Int, m.sicht 1 = 2 ∧
      m.sicht 1 ≤ beitrag Ordnung.freigabe 0 m 1 ∧
      beitrag Ordnung.entspannt 0 m 1 = 0 ∧
      beitrag Ordnung.entspannt 0 m 1 < m.sicht 1 := by
  refine ⟨⟨5, 7, fun y => if y = 1 then 2 else 0⟩,
    by decide, by decide, by decide, by decide⟩

/- CUTS:
    - No source lowering: nothing here maps a source shared-atomic access
      to target bytes; the per-access TSO simulation into W/GX, the
      granularity bridge (byte TSO vs carrier W steps) and any
      `SchrittW`/`RufSchrittGX` correspondence stay with the bridge.
    - No foreign drain: `freigabe_braucht_flush` shows a release store is
      invisible off-core until flushed, and a local fence never drains a
      foreign buffer (`zaun_kein_fremd_drain` in TSO.lean, reused, not
      duplicated). Message-passing end-to-end (flag seen implies data
      seen across cores) is NOT proved here.
    - No multi-byte atomicity: all target facts are per-byte; aligned-word
      single-copy atomicity, tearing beyond `paket_reisst` and LOCK RMW
      stay with TSO.lean §9 / LockedOps.lean.
    - No `seq_cst` total order: `SeqCstTotal` is empty
      (`kein_seqcst_total`); `seq_cst` modelled as release/acquire is a
      documented over-approximation, not a hardware claim.
    - No payload safety: source view facts speak about timestamps and
      views only; no claim about published payload values or contract
      duties (`NutzerPflichtA`, `Vertrag`) is made.
    - No progress, fairness, timing or cost: drains are reachability
      facts; flush liveness, spin bounds and cycle costs are out of scope.
    - No interrupt, device, MMIO or code-modelling claim: addresses are
      taken as `Adresse`, not decoded bytes.
-/

#print axioms freigabe_beitrag_deckt_sicht
#print axioms freigabe_nachricht_traegt_sicht
#print axioms freigabe_nachricht_eigen
#print axioms entspannt_beitrag_fremd_leer
#print axioms freigabe_liest_uebertraegt
#print axioms leer_liest_kanonisch
#print axioms zaun_erwerb_liest_kanonisch
#print axioms freigabe_braucht_flush
#print axioms freigabe_flush_sichtbar
#print axioms fifo_zweite_flush
#print axioms release_braucht_keinen_zaun
#print axioms kein_seqcst_total
#print axioms freigabe_braucht_flush_zeuge
#print axioms freigabe_sichtbar_zeuge
#print axioms freigabe_entspannt_zeuge

end Gabbro.Grammatik.X86
