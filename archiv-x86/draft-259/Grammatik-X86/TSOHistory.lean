/-
  File:      Grammatik/X86/TSOHistory.lean
  Subject:   Canonical byte-TSO history/view projection (intermediate layer).

  Lane 567 (wave B, Lean-first): the ONE reusable target-to-`Sicht`
  history/view projection over the canonical `TSOZustand` of
  `Grammatik.X86.TSO` (`issueByte`, `loadByte`, `flushKern`), instantiated
  at `Adresse`/`Byte`, for consumers BridgeWrite573 and BridgeRead574.
  Finite issue/flush sequences build fresh source messages and
  FIFO-consistent observations; youngest-own-store forwarding is handled
  through `neuestens` splits, not just flush order. No new executor, no
  fairness, no source change. Address/Byte is an intermediate layer only:
  the typed-carrier W/GX mapping and multi-byte atomicity stay CUTS.
-/
import Grammatik.X86.TSO
import Grammatik.Speichermodell.Sicht

namespace Gabbro.Grammatik.X86

/-- Committed history projection: every address holds its initial message
    `⟨0, 0, ∅⟩` (the shape `LZustand.start` uses) plus its CURRENT canonical
    byte at timestamp 1. Only flushes change it (`issue_kein_speicher`);
    pending own-buffer entries are deliberately NOT in it (they are
    invisible to foreign cores until flushed). -/
def histVon (s : TSOZustand) :
    Adresse → List (Speichermodell.Nachricht Adresse Byte) :=
  fun a => [⟨0, 0, Speichermodell.Sicht.null⟩,
    ⟨1, s.mem.bytes a, Speichermodell.Sicht.null⟩]

/-- Per-core view projection: core `c` knows address `a` at timestamp 1
    exactly when it holds a pending own-buffer entry for `a` (the
    forwarding case); otherwise its view of `a` is 0. A view never claims
    a foreign pending entry. -/
def sichtVon (s : TSOZustand) (c : Nat) : Speichermodell.Sicht Adresse :=
  fun a => match neuestens (s.puffer c) a with
    | some _ => 1
    | none => 0

/-- Every per-core view is bounded by timestamp 1: no view outruns the
    committed history, so timestamp 2 is always fresh (`Frisch`). -/
theorem sichtVon_le_eins (s : TSOZustand) (c : Nat) (a : Adresse) :
    sichtVon s c a ≤ 1 := by
  unfold sichtVon
  cases _ : neuestens (s.puffer c) a with
  | some _ => exact Nat.le_refl 1
  | none => exact Nat.zero_le 1

/-- The current canonical byte message is in the projected history. -/
theorem histVon_mem (s : TSOZustand) (a : Adresse) :
    (⟨1, s.mem.bytes a, Speichermodell.Sicht.null⟩ :
      Speichermodell.Nachricht Adresse Byte) ∈ histVon s a := by
  simp [histVon]

/-- The committed byte is readable at every core's projected view: the
    view never exceeds timestamp 1 (`sichtVon_le_eins`). -/
theorem histVon_lesbar (s : TSOZustand) (c : Nat) (a : Adresse) :
    Speichermodell.Lesbar (histVon s) (sichtVon s c) a
      ⟨1, s.mem.bytes a, Speichermodell.Sicht.null⟩ :=
  ⟨histVon_mem s a, sichtVon_le_eins s c a⟩

/-! ## Forwarding shape: the youngest own entry wins -/

/-- No match means no entry for `a` anywhere in the buffer: every entry
    addresses something else. Induction over the buffer; the head match
    decides, the tail carries the hypothesis. -/
theorem neuestens_none_kein (l : List TSOEintrag) (a : Adresse)
    (h : neuestens l a = none) (e : TSOEintrag) (hm : e ∈ l) :
    e.addr ≠ a := by
  induction l with
  | nil => simp at hm
  | cons f rest ih =>
    cases hr : neuestens rest a with
    | some w =>
      unfold neuestens at h
      rw [hr] at h
      cases h
    | none =>
      unfold neuestens at h
      rw [hr] at h
      simp only at h
      by_cases hf : f.addr = a
      · rw [if_pos hf] at h
        cases h
      · rw [if_neg hf] at h
        simp at hm
        rcases hm with rfl | hm
        · exact hf
        · exact ih hr hm

/-- A match is the YOUNGEST entry for `a`: the buffer splits into an
    older prefix, the matching entry, and a younger suffix with no entry
    for `a`. The recursion takes the tail's match when it exists (younger
    wins); otherwise the head matches and the whole tail is match-free
    (`neuestens_none_kein`). -/
theorem neuestens_jüngste (l : List TSOEintrag) (a : Adresse) (v : Byte)
    (h : neuestens l a = some v) :
    ∃ pre post : List TSOEintrag, ∃ w : Byte,
      l = pre ++ [⟨a, w⟩] ++ post ∧ w = v ∧
        ∀ e' ∈ post, e'.addr ≠ a := by
  induction l with
  | nil =>
    unfold neuestens at h
    cases h
  | cons f rest ih =>
    unfold neuestens at h
    cases hr : neuestens rest a with
    | some w =>
      rw [hr] at h
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨pre, post, w', hsplit, hw, hpost⟩ := ih hr
      exact ⟨f :: pre, post, w', by rw [hsplit]; rfl, hw, hpost⟩
    | none =>
      rw [hr] at h
      simp only at h
      by_cases hf : f.addr = a
      · obtain ⟨addr, wert⟩ := f
        simp only at hf
        rw [hf] at h ⊢
        rw [if_pos rfl] at h
        simp only [Option.some.injEq] at h
        subst h
        refine ⟨[], rest, wert, rfl, rfl, ?_⟩
        intro e' hm
        exact neuestens_none_kein rest a hr e' hm
      · rw [if_neg hf] at h
        cases h

/-! ## Loads meet the projected history -/

/-- An unforwarded load reads the canonical byte, hence the committed
    message at its actual value: `load_ohne_eintrag` pins the value, and
    the history carries it readably. -/
theorem load_lesbar_ohne_weiterleitung (s : TSOZustand) (c : Nat)
    (a : Adresse) (v : Byte)
    (hmiss : neuestens (s.puffer c) a = none)
    (hrd : s.mem.lesbar a = true)
    (hload : loadByte s c a = some v) :
    v = s.mem.bytes a ∧
      Speichermodell.Lesbar (histVon s) (sichtVon s c) a
        ⟨1, v, Speichermodell.Sicht.null⟩ := by
  have hval := load_ohne_eintrag s c a hmiss hrd
  simp only [hval, Option.some.injEq] at hload
  subst hload
  exact ⟨rfl, histVon_lesbar s c a⟩

/-- A forwarded load returns the youngest own-buffer value AND that entry
    is the youngest for `a` in the buffer: the value link comes from the
    load equation, the split from `neuestens_jüngste`. No premise is
    dropped: `hload` ties `v` to the buffer, `hpend` exhibits the match. -/
theorem weiterleitung_ist_jüngste (s : TSOZustand) (c : Nat)
    (a : Adresse) (v w : Byte)
    (hload : loadByte s c a = some v)
    (hpend : neuestens (s.puffer c) a = some w) :
    v = w ∧ ∃ pre post : List TSOEintrag,
      s.puffer c = pre ++ [⟨a, w⟩] ++ post ∧
        ∀ e' ∈ post, e'.addr ≠ a := by
  unfold loadByte at hload
  by_cases hrd : s.mem.lesbar a = true
  · rw [if_pos hrd] at hload
    rw [hpend] at hload
    simp only [Option.some.injEq] at hload
    subst hload
    obtain ⟨pre, post, w', hsplit, hw, hpost⟩ := neuestens_jüngste _ a w hpend
    subst hw
    exact ⟨rfl, pre, post, hsplit, hpost⟩
  · rw [if_neg hrd] at hload
    cases hload

/-! ## Finite issue/flush sequences build fresh messages -/

/-- Issue changes no canonical byte (`issue_kein_speicher`), so the
    projected history is pointwise unchanged: an issue is globally
    invisible until its flush. -/
theorem issue_hist_bleibt (s s' : TSOZustand) (c : Nat)
    (a : Adresse) (v : Byte)
    (h : issueByte s c a v = some s') (x : Adresse) :
    histVon s' x = histVon s x := by
  simp only [histVon, issue_kein_speicher s s' c a v h x]

/-- A flush builds a fresh source message: timestamp 2 is `Frisch` for the
    OLD history at the flushed address (every view stays below 2, every
    used timestamp is 0 or 1), and the flushed value is `Lesbar` in the
    NEW history at its actual value. -/
theorem spülen_baut_frische_nachricht (s s' : TSOZustand) (c : Nat)
    (e : TSOEintrag) (rest : List TSOEintrag)
    (h : flushKern s c = some s')
    (he : s.puffer c = e :: rest) :
    Speichermodell.Frisch (histVon s) (sichtVon s c) e.addr 2 ∧
      Speichermodell.Lesbar (histVon s') (sichtVon s' c) e.addr
        ⟨1, e.wert, Speichermodell.Sicht.null⟩ := by
  have hbytes : s'.mem.bytes e.addr = e.wert :=
    flush_schreibt_kopf s s' c h e rest he
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have hle := sichtVon_le_eins s c e.addr
    omega
  · intro m hm
    simp only [histVon, List.mem_cons] at hm
    rcases hm with rfl | htail
    · show (0 : Nat) ≠ 2
      decide
    · rcases htail with rfl | hempty
      · show (1 : Nat) ≠ 2
        decide
      · simp at hempty
  · have hm := histVon_mem s' e.addr
    rw [hbytes] at hm
    exact ⟨hm, sichtVon_le_eins s' c e.addr⟩

/-- FIFO order reaches the projected history: after two issues from
    an empty buffer and one flush, the OLDER value is the readable
    committed byte at the first address (`fifo_reihenfolge` pins the
    bytes; the history carries them). -/
theorem fifo_hist_konsistent (s s1 s2 s3 : TSOZustand) (c : Nat)
    (a b : Adresse) (v w : Byte)
    (h1 : issueByte s c a v = some s1)
    (h2 : issueByte s1 c b w = some s2)
    (hempty : s.puffer c = [])
    (h3 : flushKern s2 c = some s3) :
    Speichermodell.Lesbar (histVon s3) (sichtVon s3 c) a
      ⟨1, v, Speichermodell.Sicht.null⟩ := by
  have hbytes : s3.mem.bytes a = v :=
    fifo_reihenfolge s s1 s2 s3 c a b v w h1 h2 hempty h3
  have hm := histVon_mem s3 a
  rw [hbytes] at hm
  exact ⟨hm, sichtVon_le_eins s3 c a⟩

/-! ## Concrete same-core two-issue witness (for tearing) -/

/-- After core 0 additionally issues `sbY := 1` on top of `sbNach1`. -/
def hS2 : TSOZustand :=
  ⟨zeugenSpeicher,
    pufferSetze sbNach1.puffer 0 (sbNach1.puffer 0 ++ [⟨sbY, sbEins⟩])⟩

/-- After core 0 flushes its oldest entry (`sbX`). -/
def hS3 : TSOZustand :=
  ⟨{ sbNach1.mem with
      bytes := fun x => if x = sbX then sbEins else sbNach1.mem.bytes x },
    pufferSetze hS2.puffer 0 [⟨sbY, sbEins⟩]⟩

/-- The second same-core issue computes as claimed. -/
theorem h_schritt2 : issueByte sbNach1 0 sbY sbEins = some hS2 := by
  rfl

/-- The flush of the oldest entry computes as claimed. -/
theorem h_flush : flushKern hS2 0 = some hS3 := by
  rfl

/-- **Tearing, observed.** Two same-core issued bytes flush one at a
    time: after the first flush the first address is new while the second
    still reads the pre-flush byte (`paket_reisst`). No multi-byte
    atomicity is claimed at this layer. -/
theorem hist_zerreissen :
    hS3.mem.bytes sbX = sbEins ∧
      hS3.mem.bytes sbY = hS2.mem.bytes sbY :=
  paket_reisst sbStart sbNach1 hS2 hS3 0 sbX sbY sbEins sbEins
    sb_schritt1 h_schritt2 rfl h_flush sbX_ne_sbY

/-! ## Refusal: foreign pending stores are invisible -/

/-- **REFUSAL (proved): a locally fence-ready core coexists with a foreign
    forwarded read past canonical memory, and the forwarded value has NO
    message in the committed history.** Core 0 is fence-ready while core 1
    forwards its own pending `7` at address 0 over the canonical `0`. An
    issue is not global visibility; only flushes publish. -/
theorem fremd_weiterleitung_unsichtbar :
    ∃ (s : TSOZustand) (a : Adresse) (v : Byte),
      zaunBereit s 0 = true ∧ s.puffer 1 ≠ [] ∧
      loadByte s 1 a = some v ∧ v ≠ s.mem.bytes a ∧
        ∀ m ∈ histVon s a, m.wert ≠ v := by
  refine ⟨⟨zeugenSpeicher,
    fun d => if d = 1 then [⟨(0 : Adresse), BitVec.ofNat 8 7⟩] else []⟩,
    0, BitVec.ofNat 8 7,
    by decide, by decide, by decide, by decide, ?_⟩
  intro m hm
  simp only [histVon, zeugenSpeicher, List.mem_cons,
    List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl <;> decide

/-! ## Joint witness: reached, two-core, memory-changing -/

/-- **JOINT WITNESS.** From the empty start, two issues on different cores
    reach `sbNach2` (both cores load the stale `0` for the other's
    address); flushing core 0 observably changes the canonical byte at
    `sbX`, and the flushed value is readable in the projected history at
    its actual value. Non-degenerate: two cores, real buffered stores, a
    memory-changing flush. -/
theorem hist_zeuge_gelenk :
    TSOErreichbar sbStart sbNach2 ∧
    loadByte sbNach2 0 sbY = some 0 ∧ loadByte sbNach2 1 sbX = some 0 ∧
    flushKern sbNach2 0 = some sbGespült ∧
    sbNach2.mem.bytes sbX ≠ sbGespült.mem.bytes sbX ∧
    Speichermodell.Lesbar (histVon sbGespült) (sichtVon sbGespült 0) sbX
      ⟨1, sbEins, Speichermodell.Sicht.null⟩ := by
  have hbuf : sbNach2.puffer 0 = [⟨sbX, sbEins⟩] := by
    show pufferSetze sbNach1.puffer 1 [⟨sbY, sbEins⟩] 0 = _
    rw [pufferSetze_anders _ _ (by decide)]
    show pufferSetze sbStart.puffer 0 [⟨sbX, sbEins⟩] 0 = _
    exact pufferSetze_gleich _ _ _
  have hbytes : sbGespült.mem.bytes sbX = sbEins :=
    flush_schreibt_kopf sbNach2 sbGespült 0 sb_flush_schritt _ [] hbuf
  have hm := histVon_mem sbGespült sbX
  rw [hbytes] at hm
  exact ⟨.schritt (.schritt .start (.issue _ _ _ _ _ sb_schritt1))
      (.issue _ _ _ _ _ sb_schritt2),
    sb_beide_laden_null.1, sb_beide_laden_null.2,
    sb_flush_schritt, sb_flush_aendert_speicher,
    hm, sichtVon_le_eins _ _ _⟩

/- CUTS:
    - Address/Byte is an INTERMEDIATE layer only: no typed-carrier W/GX
      mapping (carrier-granular histories, `GeteiltV`/`HavocA` atomic
      environments), no aligned multi-byte single-copy atomicity
      (`hist_zerreissen` shows tearing), no LOCK RMW.
    - No per-access `SchrittW` (`wahl`/`neu`) construction, no G-step
      access-list decomposition (O-access of TSO-GX-BRUECKE.md), no run
      induction from x86 traces to W runs: consumers BridgeWrite573 and
      BridgeRead574 own that; this module hands them `histVon`,
      `sichtVon`, fresh-message and youngest-forwarding facts.
    - The timestamp discipline (0 initial, 1 committed, 2 fresh) is
      projection-local: no claim that source W timestamps coincide with
      these; `Frisch ... 2` is the shape a flush-built message takes.
    - No fairness, progress, timing or cycle-cost claim; no interrupt,
      device, MMIO or DMA model; fences only gate (`zaunBereit` reused).
    - No new TSO executor: `TSOZustand`, `issueByte`, `loadByte`,
      `flushKern`, `TSOErreichbar`, `sb*` witnesses and `paket_reisst`
      are reused unchanged from `Grammatik.X86.TSO`.
-/

#print axioms sichtVon_le_eins
#print axioms histVon_mem
#print axioms histVon_lesbar
#print axioms neuestens_none_kein
#print axioms neuestens_jüngste
#print axioms load_lesbar_ohne_weiterleitung
#print axioms weiterleitung_ist_jüngste
#print axioms issue_hist_bleibt
#print axioms spülen_baut_frische_nachricht
#print axioms fifo_hist_konsistent
#print axioms h_schritt2
#print axioms h_flush
#print axioms hist_zerreissen
#print axioms fremd_weiterleitung_unsichtbar
#print axioms hist_zeuge_gelenk

end Gabbro.Grammatik.X86
