/-
  File:      Grammatik/X86/WordDrainInterleaving.lean
  Subject:   Whole-word drain across a trace with real interleaved
             foreign accesses.

  Lane 652: consumer of the ACCEPTED `WordAccessGrouping` (603)
  vocabulary (`WortGruppe`, `FremdFrei`, `DrainSchritt`, `DrainSpur`,
  canonical `issueByte`/`flushKern`). The pure own-drain witness of 603
  is insufficient here: this module derives grouped read-back and
  foreign-word preservation across a drain trace that contains an
  actual foreign issue AND an actual foreign flush between own
  flushes. Trace exclusion is derived from finite footprint checks on
  real buffer accesses, never from assumed end-state equality. No
  hardware-atomicity claim (each flush moves one byte), no LOCK
  source refinement, no fairness or timing premise.
-/
import Grammatik.X86.WordAccessGrouping

namespace Gabbro.Grammatik.X86

/-- Grouped word base address: zero (aligned). -/
def vA : Adresse := 0

/-- Foreign word base address: 8192 (disjoint, no wrap). -/
def vB : Adresse := BitVec.ofNat 64 8192

/-- Foreign byte value: 7 (nonzero, so the foreign write is visible). -/
def fByte : Byte := BitVec.ofNat 8 7

/-! ## 1. Finite footprint checks: exclusion from real accesses. -/

/-- Decidable per-entry check: the entry address avoids footprint `a`.
    Inspects the real pending entry, not a desired end state. -/
def eintragFrei (e : TSOEintrag) (a : Adresse) : Bool :=
  decide (e.addr ∉ Fuss a)

/-- Decidable per-buffer check: every pending entry avoids `a`. -/
def pufferFrei (l : List TSOEintrag) (a : Adresse) : Bool :=
  l.all (fun e => eintragFrei e a)

/-- The per-entry check means what it says. -/
theorem eintragFrei_gilt (e : TSOEintrag) (a : Adresse)
    (h : eintragFrei e a = true) : e.addr ∉ Fuss a := by
  unfold eintragFrei at h
  exact of_decide_eq_true h

/-- The per-buffer check means what it says: finite conjunction over
    the real pending entries. -/
theorem pufferFrei_gilt (l : List TSOEintrag) (a : Adresse)
    (h : pufferFrei l a = true) (e : TSOEintrag) (hm : e ∈ l) :
    e.addr ∉ Fuss a := by
  unfold pufferFrei at h
  rw [List.all_eq_true] at h
  exact eintragFrei_gilt e a (h e hm)

/-- Two-core exclusion from finite checks: core 1 passes the list
    check at `a` and every other foreign core is empty. No premise
    is dropped: `h1` covers core 1, `hRest` every other core. -/
theorem fremdFrei_von_pruefung (s : TSOZustand) (a : Adresse)
    (h1 : ∀ e ∈ s.puffer 1, e.addr ∉ Fuss a)
    (hRest : ∀ d : Nat, d ≠ 0 → d ≠ 1 → s.puffer d = []) :
    FremdFrei s 0 a := by
  intro d hne e he
  by_cases hd : d = 1
  · subst hd
    exact h1 e he
  · rw [hRest d hne hd] at he
    simp at he

/-- Trace exclusion from per-state finite checks: every visited state
    passes the core-1 list check and keeps other cores empty. -/
theorem spurFrei_von_pruefung (t : List TSOZustand) (a : Adresse)
    (h1 : ∀ x ∈ t, ∀ e ∈ x.puffer 1, e.addr ∉ Fuss a)
    (hRest : ∀ x ∈ t, ∀ d : Nat, d ≠ 0 → d ≠ 1 → x.puffer d = []) :
    ∀ x ∈ t, FremdFrei x 0 a := by
  intro x hx
  exact fremdFrei_von_pruefung x a (h1 x hx) (hRest x hx)

/-! ## 2. Generic drain consequences under checked exclusion. -/

/-- INTERLEAVED READ-BACK (generic): the 603 grouped read-back with
    its exclusion derived from finite per-state checks on the real
    foreign buffers. Every premise is used: the group pins the start
    buffer, readability the final load, the trace the installed
    prefix, end membership the witness state, emptiness the full
    eight, and the two checks every foreign step along the way. -/
theorem verflochten_liest_zurueck (s2 sN : TSOZustand)
    (t : List TSOZustand) (a : Adresse) (v : Wort)
    (hgrp : WortGruppe s2 0 a v) (hles : lesbar8 s2.mem a = true)
    (hspur : DrainSpur 0 s2 sN t) (hend : sN ∈ t)
    (hleer : sN.puffer 0 = [])
    (h1 : ∀ x ∈ t, ∀ e ∈ x.puffer 1, e.addr ∉ Fuss a)
    (hRest : ∀ x ∈ t, ∀ d : Nat, d ≠ 0 → d ≠ 1 → x.puffer d = []) :
    read64 sN.mem a = some v :=
  wort_gruppe_liest_zurueck s2 sN t 0 a v hgrp hles hspur hend hleer
    (spurFrei_von_pruefung t a h1 hRest)

/-- OWN FIFO RETAINED (generic): at every visited state the acting
    buffer is a suffix of the canonical eight-entry list. The group
    pins the start buffer, the trace the installed prefix, the
    exclusion every foreign step. -/
theorem verflochten_fifo_suffix (s2 sN : TSOZustand)
    (t : List TSOZustand) (a : Adresse) (v : Wort)
    (hgrp : WortGruppe s2 0 a v)
    (hspur : DrainSpur 0 s2 sN t)
    (hstoer : ∀ x ∈ t, FremdFrei x 0 a)
    (x : TSOZustand) (hx : x ∈ t) :
    ∃ k' : Nat, k' ≤ 8 ∧ x.puffer 0 = (wortEintraege a v).drop k' := by
  obtain ⟨hbufl, _hff⟩ := hgrp
  have hbase : s2.puffer 0 = (wortEintraege a v).drop 0 := by
    rw [hbufl]
    rfl
  obtain ⟨k', _hk0, hk'8, hbufN, _hmemN⟩ :=
    drain_installiert_aux 0 a v s2 sN t hspur hstoer 0 (Nat.zero_le 8)
      hbase (fun j hj => absurd hj (by omega)) x hx
  exact ⟨k', hk'8, hbufN⟩

/-- Every canonical group entry sits on the footprint. -/
theorem worteintrag_in_fuss (a : Adresse) (v : Wort) (e : TSOEintrag)
    (hm : e ∈ wortEintraege a v) : e.addr ∈ Fuss a := by
  simp only [wortEintraege, List.mem_cons, List.not_mem_nil,
    or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fuss_mem_offset a 0 (by decide)
  · exact fuss_mem_offset a 1 (by decide)
  · exact fuss_mem_offset a 2 (by decide)
  · exact fuss_mem_offset a 3 (by decide)
  · exact fuss_mem_offset a 4 (by decide)
  · exact fuss_mem_offset a 5 (by decide)
  · exact fuss_mem_offset a 6 (by decide)
  · exact fuss_mem_offset a 7 (by decide)

/-- Suffix entries sit on the footprint too: drain order never leaves
    the grouped footprint. -/
theorem suffix_eintrag_in_fuss (a : Adresse) (v : Wort) (k : Nat)
    (e : TSOEintrag) (hm : e ∈ (wortEintraege a v).drop k) :
    e.addr ∈ Fuss a :=
  worteintrag_in_fuss a v e (List.drop_subset k (wortEintraege a v) hm)

/-- FOREIGN DISJOINT WRITE PRESERVED ACROSS AN OWN FLUSH (generic):
    an own flush installs a footprint-`a` member only, so every byte
    of a disjoint footprint `b` survives. The own-buffer footprint
    membership, disjointness and the flush equation are all used. -/
theorem verflochten_fremd_bleibt (s s' : TSOZustand)
    (a b : Adresse)
    (hdis : Disjunkt a b)
    (hown : ∀ e : TSOEintrag, e ∈ s.puffer 0 → e.addr ∈ Fuss a)
    (hfl : flushKern s 0 = some s') (k : Nat) (hk : k < 8) :
    s'.mem.bytes (addrOff b k) = s.mem.bytes (addrOff b k) := by
  match hpd : s.puffer 0 with
  | [] =>
    have hnone : flushKern s 0 = none := flush_leer s 0 hpd
    rw [hnone] at hfl
    cases hfl
  | e :: rest =>
    have he_foot : e.addr ∈ Fuss a := hown e (hpd ▸ by simp)
    obtain ⟨j, hj8, hj⟩ := (fuss_mem_iff a _).mp he_foot
    have hne : addrOff b k ≠ e.addr := by
      rw [← hj]
      exact Ne.symm (hdis j k hj8 hk)
    exact flush_rahmen s s' 0 hfl e rest hpd _ hne

/-- FOREIGN FLUSH INSTALLS ITS BYTE (generic): the flushed value
    lands at its address. The equation and both entry facts are used. -/
theorem verflochten_fremd_installiert (s s' : TSOZustand)
    (b : Adresse) (w : Byte)
    (hfl : flushKern s 1 = some s') (e : TSOEintrag)
    (rest : List TSOEintrag)
    (he : s.puffer 1 = e :: rest) (ha : e.addr = b) (hv : e.wert = w) :
    s'.mem.bytes b = w := by
  have h := flush_schreibt_kopf s s' 1 hfl e rest he
  rw [ha, hv] at h
  exact h

/-! ## 3. Interleaved witness: foreign issue and flush between own flushes. -/

/-- Witness start: the exact eight-entry group on core 0 (603 state),
    foreign buffers empty. -/
def wI0 : TSOZustand := grpS2

/-- After own flush 1: byte 0 installed (603 state). -/
def wI1 : TSOZustand := grpS3

/-- After the foreign issue on core 1 at `vB`: memory-silent. -/
def wI2 : TSOZustand :=
  ⟨wI1.mem, pufferSetze wI1.puffer 1 [⟨vB, fByte⟩]⟩

/-- After the foreign flush on core 1: `vB` carries `fByte`. -/
def wI3 : TSOZustand :=
  ⟨{ wI2.mem with bytes := fun x => if x = vB then fByte else wI2.mem.bytes x },
    pufferSetze wI2.puffer 1 []⟩

/-- After own flush 2: bytes 0-1 installed, foreign byte carried. -/
def wI4 : TSOZustand :=
  ⟨{ wI3.mem with bytes := fun x =>
      if (x = addrOff vA 1) then wortByte zeugenWort 1
      else wI3.mem.bytes x },
    pufferSetze wI3.puffer 0 ((wortEintraege vA zeugenWort).drop 2)⟩

/-- After own flush 3: bytes 0-2 installed. -/
def wI5 : TSOZustand :=
  ⟨{ wI4.mem with bytes := fun x =>
      if (x = addrOff vA 2) then wortByte zeugenWort 2
      else wI4.mem.bytes x },
    pufferSetze wI4.puffer 0 ((wortEintraege vA zeugenWort).drop 3)⟩

/-- After own flush 4: bytes 0-3 installed. -/
def wI6 : TSOZustand :=
  ⟨{ wI5.mem with bytes := fun x =>
      if (x = addrOff vA 3) then wortByte zeugenWort 3
      else wI5.mem.bytes x },
    pufferSetze wI5.puffer 0 ((wortEintraege vA zeugenWort).drop 4)⟩

/-- After own flush 5: bytes 0-4 installed. -/
def wI7 : TSOZustand :=
  ⟨{ wI6.mem with bytes := fun x =>
      if (x = addrOff vA 4) then wortByte zeugenWort 4
      else wI6.mem.bytes x },
    pufferSetze wI6.puffer 0 ((wortEintraege vA zeugenWort).drop 5)⟩

/-- After own flush 6: bytes 0-5 installed. -/
def wI8 : TSOZustand :=
  ⟨{ wI7.mem with bytes := fun x =>
      if (x = addrOff vA 5) then wortByte zeugenWort 5
      else wI7.mem.bytes x },
    pufferSetze wI7.puffer 0 ((wortEintraege vA zeugenWort).drop 6)⟩

/-- After own flush 7: bytes 0-6 installed. -/
def wI9 : TSOZustand :=
  ⟨{ wI8.mem with bytes := fun x =>
      if (x = addrOff vA 6) then wortByte zeugenWort 6
      else wI8.mem.bytes x },
    pufferSetze wI8.puffer 0 ((wortEintraege vA zeugenWort).drop 7)⟩

/-- After own flush 8: all group bytes installed, own buffer empty,
    foreign buffer empty, foreign byte intact. -/
def wI10 : TSOZustand :=
  ⟨{ wI9.mem with bytes := fun x =>
      if (x = addrOff vA 7) then wortByte zeugenWort 7
      else wI9.mem.bytes x },
    pufferSetze wI9.puffer 0 ((wortEintraege vA zeugenWort).drop 8)⟩

/-- Own flush 1 computes as claimed (603 equation, reused). -/
theorem wI_e1 : flushKern wI0 0 = some wI1 := grp_step1

/-- The foreign issue computes as claimed: memory-silent. -/
theorem wI_issue : issueByte wI1 1 vB fByte = some wI2 := by rfl

/-- The foreign flush computes as claimed. -/
theorem wI_fflush : flushKern wI2 1 = some wI3 := by rfl

/-- Own flush 2 computes as claimed. -/
theorem wI_e2 : flushKern wI3 0 = some wI4 := by rfl

/-- Own flush 3 computes as claimed. -/
theorem wI_e3 : flushKern wI4 0 = some wI5 := by rfl

/-- Own flush 4 computes as claimed. -/
theorem wI_e4 : flushKern wI5 0 = some wI6 := by rfl

/-- Own flush 5 computes as claimed. -/
theorem wI_e5 : flushKern wI6 0 = some wI7 := by rfl

/-- Own flush 6 computes as claimed. -/
theorem wI_e6 : flushKern wI7 0 = some wI8 := by rfl

/-- Own flush 7 computes as claimed. -/
theorem wI_e7 : flushKern wI8 0 = some wI9 := by rfl

/-- Own flush 8 computes as claimed. -/
theorem wI_e8 : flushKern wI9 0 = some wI10 := by rfl

/-! ## 4. Footprint separation and per-state buffer facts. -/

/-- The foreign address lies outside the grouped footprint: finite
    membership check on the real footprint list. -/
theorem vB_ausserhalb : vB ∉ Fuss vA := by decide

/-- The two word footprints are disjoint: interval order under
    no-wrap on both sides. -/
theorem vA_vB_disjunkt : Disjunkt vA vB := by
  have hA : OhneUmbruch vA := by unfold OhneUmbruch; decide
  have hB : OhneUmbruch vB := by unfold OhneUmbruch; decide
  have hle : vA.toNat + 8 ≤ vB.toNat := by decide
  exact disjunkt_von_intervallen _ _ hA hB (Or.inl hle)

/-- The witness start satisfies the grouping check (603 fact, reused:
    exact eight-entry buffer, empty foreign buffers). -/
theorem wI_hgrp : WortGruppe wI0 0 vA zeugenWort := grp_hgrp

/-- The witness start reads the grouped footprint. -/
theorem wI_hles : lesbar8 wI0.mem vA = true := grp_hles

/-! ## 5. Small preservation steps for the interleaved shape. -/

/-- An own flush keeps every other core's buffer: rest-emptiness
    survives. Both premises are used. -/
theorem eigen_rest_erhalten (s s' : TSOZustand)
    (hfl : flushKern s 0 = some s')
    (hleer : ∀ d : Nat, d ≠ 0 → d ≠ 1 → s.puffer d = []) :
    ∀ d : Nat, d ≠ 0 → d ≠ 1 → s'.puffer d = [] := by
  intro d hd0 hd1
  have hsame : s'.puffer d = s.puffer d :=
    flush_anderer_kern s s' 0 hfl hd0
  rw [hsame]
  exact hleer d hd0 hd1

/-- A core-1 issue keeps every other core's buffer. -/
theorem fremd1_issue_rest_erhalten (s s' : TSOZustand)
    (a : Adresse) (w : Byte)
    (h : issueByte s 1 a w = some s')
    (hleer : ∀ d : Nat, d ≠ 0 → d ≠ 1 → s.puffer d = []) :
    ∀ d : Nat, d ≠ 0 → d ≠ 1 → s'.puffer d = [] := by
  intro d hd0 hd1
  have hsame : s'.puffer d = s.puffer d :=
    issue_anderer_kern s s' 1 a w h hd1
  rw [hsame]
  exact hleer d hd0 hd1

/-- A core-1 flush keeps every other core's buffer. -/
theorem fremd1_flush_rest_erhalten (s s' : TSOZustand)
    (hfl : flushKern s 1 = some s')
    (hleer : ∀ d : Nat, d ≠ 0 → d ≠ 1 → s.puffer d = []) :
    ∀ d : Nat, d ≠ 0 → d ≠ 1 → s'.puffer d = [] := by
  intro d hd0 hd1
  have hsame : s'.puffer d = s.puffer d :=
    flush_anderer_kern s s' 1 hfl hd1
  rw [hsame]
  exact hleer d hd0 hd1

/-- An own flush keeps core 1's buffer: the foreign list fact travels. -/
theorem eigen_puffer1_bleibt (s s' : TSOZustand)
    (hfl : flushKern s 0 = some s') :
    s'.puffer 1 = s.puffer 1 :=
  flush_anderer_kern s s' 0 hfl (by decide)

/-- Rest-emptiness at the witness start and after own flush 1. -/
theorem wI0_rest : ∀ d : Nat, d ≠ 0 → d ≠ 1 → wI0.puffer d = [] :=
  fun d h0 _ => grpS2_fremd_leer d h0

theorem wI1_rest : ∀ d : Nat, d ≠ 0 → d ≠ 1 → wI1.puffer d = [] :=
  fun d h0 _ => grpS3_fremd_leer d h0

/-- Rest-emptiness past the foreign issue and flush. -/
theorem wI2_rest : ∀ d : Nat, d ≠ 0 → d ≠ 1 → wI2.puffer d = [] :=
  fremd1_issue_rest_erhalten wI1 wI2 vB fByte wI_issue wI1_rest

theorem wI3_rest : ∀ d : Nat, d ≠ 0 → d ≠ 1 → wI3.puffer d = [] :=
  fremd1_flush_rest_erhalten wI2 wI3 wI_fflush wI2_rest

/-- Rest-emptiness down the remaining own drain. -/
theorem wI4_rest : ∀ d : Nat, d ≠ 0 → d ≠ 1 → wI4.puffer d = [] :=
  eigen_rest_erhalten wI3 wI4 wI_e2 wI3_rest

theorem wI5_rest : ∀ d : Nat, d ≠ 0 → d ≠ 1 → wI5.puffer d = [] :=
  eigen_rest_erhalten wI4 wI5 wI_e3 wI4_rest

theorem wI6_rest : ∀ d : Nat, d ≠ 0 → d ≠ 1 → wI6.puffer d = [] :=
  eigen_rest_erhalten wI5 wI6 wI_e4 wI5_rest

theorem wI7_rest : ∀ d : Nat, d ≠ 0 → d ≠ 1 → wI7.puffer d = [] :=
  eigen_rest_erhalten wI6 wI7 wI_e5 wI6_rest

theorem wI8_rest : ∀ d : Nat, d ≠ 0 → d ≠ 1 → wI8.puffer d = [] :=
  eigen_rest_erhalten wI7 wI8 wI_e6 wI7_rest

theorem wI9_rest : ∀ d : Nat, d ≠ 0 → d ≠ 1 → wI9.puffer d = [] :=
  eigen_rest_erhalten wI8 wI9 wI_e7 wI8_rest

theorem wI10_rest : ∀ d : Nat, d ≠ 0 → d ≠ 1 → wI10.puffer d = [] :=
  eigen_rest_erhalten wI9 wI10 wI_e8 wI9_rest

/-! ## 6. Core-1 list facts and trace exclusion from finite checks. -/

/-- The foreign issue installs exactly one pending entry on core 1. -/
theorem wI2_p1 : wI2.puffer 1 = [⟨vB, fByte⟩] := by rfl

/-- The foreign flush drains core 1. -/
theorem wI3_p1 : wI3.puffer 1 = [] := by rfl

/-- Core 1 stays drained down the remaining own flushes. -/
theorem wI4_p1 : wI4.puffer 1 = [] := by
  rw [eigen_puffer1_bleibt wI3 wI4 wI_e2]
  exact wI3_p1

theorem wI5_p1 : wI5.puffer 1 = [] := by
  rw [eigen_puffer1_bleibt wI4 wI5 wI_e3]
  exact wI4_p1

theorem wI6_p1 : wI6.puffer 1 = [] := by
  rw [eigen_puffer1_bleibt wI5 wI6 wI_e4]
  exact wI5_p1

theorem wI7_p1 : wI7.puffer 1 = [] := by
  rw [eigen_puffer1_bleibt wI6 wI7 wI_e5]
  exact wI6_p1

theorem wI8_p1 : wI8.puffer 1 = [] := by
  rw [eigen_puffer1_bleibt wI7 wI8 wI_e6]
  exact wI7_p1

theorem wI9_p1 : wI9.puffer 1 = [] := by
  rw [eigen_puffer1_bleibt wI8 wI9 wI_e7]
  exact wI8_p1

theorem wI10_p1 : wI10.puffer 1 = [] := by
  rw [eigen_puffer1_bleibt wI9 wI10 wI_e8]
  exact wI9_p1

/-- Core 1 starts empty at the witness start and after own flush 1. -/
theorem wI0_p1 : wI0.puffer 1 = [] := grpS2_fremd_leer 1 (by decide)

theorem wI1_p1 : wI1.puffer 1 = [] := grpS3_fremd_leer 1 (by decide)

/-- The interleaved trace with its visited states. -/
def wI_trace : List TSOZustand :=
  [wI0, wI1, wI2, wI3, wI4, wI5, wI6, wI7, wI8, wI9, wI10]

/-- Core-1 list check at every visited state: the only nonempty
    foreign buffer holds the disjoint `vB` entry. Finite check on
    the real pending entries. -/
theorem wI_h1 :
    ∀ x ∈ wI_trace, ∀ e ∈ x.puffer 1, e.addr ∉ Fuss vA := by
  intro x hx e he
  simp only [wI_trace, List.mem_cons, List.not_mem_nil,
    or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [wI0_p1] at he
    simp at he
  · rw [wI1_p1] at he
    simp at he
  · rw [wI2_p1] at he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    subst he
    show vB ∉ Fuss vA
    exact vB_ausserhalb
  · rw [wI3_p1] at he
    simp at he
  · rw [wI4_p1] at he
    simp at he
  · rw [wI5_p1] at he
    simp at he
  · rw [wI6_p1] at he
    simp at he
  · rw [wI7_p1] at he
    simp at he
  · rw [wI8_p1] at he
    simp at he
  · rw [wI9_p1] at he
    simp at he
  · rw [wI10_p1] at he
    simp at he

/-- Rest-emptiness at every visited state. -/
theorem wI_hRest :
    ∀ x ∈ wI_trace, ∀ d : Nat, d ≠ 0 → d ≠ 1 → x.puffer d = [] := by
  intro x hx
  simp only [wI_trace, List.mem_cons, List.not_mem_nil,
    or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact wI0_rest
  · exact wI1_rest
  · exact wI2_rest
  · exact wI3_rest
  · exact wI4_rest
  · exact wI5_rest
  · exact wI6_rest
  · exact wI7_rest
  · exact wI8_rest
  · exact wI9_rest
  · exact wI10_rest

/-- Trace exclusion, derived from the finite per-state checks above
    rather than assumed from the end state. -/
theorem wI_hstoer : ∀ x ∈ wI_trace, FremdFrei x 0 vA :=
  spurFrei_von_pruefung wI_trace vA wI_h1 wI_hRest

/-! ## 7. The interleaved drain trace and its generic consequences. -/

/-- Each recorded step is a drain step: own flush, foreign issue,
    foreign flush, then the remaining own flushes. -/
theorem wI_d1 : DrainSchritt 0 wI0 wI1 := .eigen wI_e1

theorem wI_dIssue : DrainSchritt 0 wI1 wI2 :=
  .fremdAusgabe 1 ⟨vB, fByte⟩ (by decide) wI_issue

theorem wI_dFlush : DrainSchritt 0 wI2 wI3 :=
  .fremdSpülen 1 (by decide) wI_fflush

theorem wI_d2 : DrainSchritt 0 wI3 wI4 := .eigen wI_e2

theorem wI_d3 : DrainSchritt 0 wI4 wI5 := .eigen wI_e3

theorem wI_d4 : DrainSchritt 0 wI5 wI6 := .eigen wI_e4

theorem wI_d5 : DrainSchritt 0 wI6 wI7 := .eigen wI_e5

theorem wI_d6 : DrainSchritt 0 wI7 wI8 := .eigen wI_e6

theorem wI_d7 : DrainSchritt 0 wI8 wI9 := .eigen wI_e7

theorem wI_d8 : DrainSchritt 0 wI9 wI10 := .eigen wI_e8

/-- The full interleaved drain trace: eight own flushes with a real
    foreign issue and a real foreign flush between flush 1 and 2. -/
theorem wI_spur : DrainSpur 0 wI0 wI10 wI_trace :=
  .schritt _ _ _ _ wI_d1 (.schritt _ _ _ _ wI_dIssue
    (.schritt _ _ _ _ wI_dFlush (.schritt _ _ _ _ wI_d2
      (.schritt _ _ _ _ wI_d3 (.schritt _ _ _ _ wI_d4
        (.schritt _ _ _ _ wI_d5 (.schritt _ _ _ _ wI_d6
          (.schritt _ _ _ _ wI_d7 (.schritt _ _ _ _ wI_d8
            (.leer wI10))))))))))

/-- The drain end is visited. -/
theorem wI_hend : wI10 ∈ wI_trace := by simp [wI_trace]

/-- The drain ends with an empty own buffer. -/
theorem wI_hempty : wI10.puffer 0 = [] := by rfl

/-- The drain ends with an empty foreign buffer. -/
theorem wI_hemptyF : wI10.puffer 1 = [] := wI10_p1

/-- The interleaved drain is a reached TSO run. -/
theorem wI_erreichbar : TSOErreichbar wI0 wI10 :=
  drain_spur_erreichbar 0 wI0 wI10 wI_trace wI_spur

/-- INTERLEAVED READ-BACK on the witness: the generic wrapper
    concludes the grouped word despite the foreign steps. -/
theorem wI_liest_zurueck : read64 wI10.mem vA = some zeugenWort :=
  verflochten_liest_zurueck wI0 wI10 wI_trace vA zeugenWort
    wI_hgrp wI_hles wI_spur wI_hend wI_hempty wI_h1 wI_hRest

/-- OWN FIFO RETAINED on the witness: every visited buffer is a
    suffix of the canonical eight-entry list. -/
theorem wI_fifo :
    ∀ x ∈ wI_trace, ∃ k' : Nat, k' ≤ 8 ∧
      x.puffer 0 = (wortEintraege vA zeugenWort).drop k' := by
  intro x hx
  exact verflochten_fifo_suffix wI0 wI10 wI_trace vA zeugenWort
    wI_hgrp wI_spur wI_hstoer x hx

/-- Every own-buffer entry on the witness sits on the footprint. -/
theorem wI_own_in_fuss (x : TSOZustand) (hx : x ∈ wI_trace) :
    ∀ e : TSOEintrag, e ∈ x.puffer 0 → e.addr ∈ Fuss vA := by
  obtain ⟨k', _hk8, hbuf⟩ := wI_fifo x hx
  intro e he
  rw [hbuf] at he
  exact suffix_eintrag_in_fuss vA zeugenWort k' e he

/-! ## 8. Foreign write: installed by its flush, kept by own flushes. -/

/-- The foreign flush installs `fByte` at `vB`. -/
theorem wI3_fremd_installiert : wI3.mem.bytes vB = fByte :=
  verflochten_fremd_installiert wI2 wI3 vB fByte wI_fflush
    ⟨vB, fByte⟩ [] wI2_p1 rfl rfl

/-- The seven later own flushes preserve the foreign byte: disjoint
    footprints, real flush frame at each step. -/
theorem wI_fremd_bleibt_kette : wI10.mem.bytes vB = wI3.mem.bytes vB := by
  have h4 := verflochten_fremd_bleibt wI3 wI4 vA vB vA_vB_disjunkt
    (wI_own_in_fuss wI3 (by simp [wI_trace])) wI_e2 0 (by decide)
  have h5 := verflochten_fremd_bleibt wI4 wI5 vA vB vA_vB_disjunkt
    (wI_own_in_fuss wI4 (by simp [wI_trace])) wI_e3 0 (by decide)
  have h6 := verflochten_fremd_bleibt wI5 wI6 vA vB vA_vB_disjunkt
    (wI_own_in_fuss wI5 (by simp [wI_trace])) wI_e4 0 (by decide)
  have h7 := verflochten_fremd_bleibt wI6 wI7 vA vB vA_vB_disjunkt
    (wI_own_in_fuss wI6 (by simp [wI_trace])) wI_e5 0 (by decide)
  have h8 := verflochten_fremd_bleibt wI7 wI8 vA vB vA_vB_disjunkt
    (wI_own_in_fuss wI7 (by simp [wI_trace])) wI_e6 0 (by decide)
  have h9 := verflochten_fremd_bleibt wI8 wI9 vA vB vA_vB_disjunkt
    (wI_own_in_fuss wI8 (by simp [wI_trace])) wI_e7 0 (by decide)
  have h10 := verflochten_fremd_bleibt wI9 wI10 vA vB vA_vB_disjunkt
    (wI_own_in_fuss wI9 (by simp [wI_trace])) wI_e8 0 (by decide)
  rw [addrOff_null] at h4 h5 h6 h7 h8 h9 h10
  exact h10.trans (h9.trans (h8.trans (h7.trans (h6.trans (h5.trans h4)))))

/-- FOREIGN DISJOINT WRITE PRESERVED on the witness: the foreign
    byte survives the whole remaining own drain. -/
theorem wI_fremd_byte : wI10.mem.bytes vB = fByte :=
  wI_fremd_bleibt_kette.trans wI3_fremd_installiert

/-- The foreign word reads back with the foreign byte installed. -/
theorem wI_fremd_wort :
    read64 wI10.mem vB = some (BitVec.ofNat 64 7) := by
  decide

/-- Both memories observably changed: grouped byte 0 and foreign `vB`. -/
theorem wI_grp_aendert : wI0.mem.bytes vA ≠ wI10.mem.bytes vA := by
  decide

theorem wI_fremd_aendert : wI0.mem.bytes vB ≠ wI10.mem.bytes vB := by
  decide

/-! ## 9. Joint witness and per-claim inhabitants. -/

/-- JOINT WITNESS: the interleaved drain is reached, drains both
    buffers, keeps every visited state foreign-free at the grouped
    footprint, keeps own FIFO shape, reads back the grouped word and
    the foreign word, changes both memories, and exhibits the actual
    foreign issue and foreign flush between own flushes. -/
theorem wI_zeuge_gelenk :
    ∃ (t : List TSOZustand) (sN : TSOZustand),
      DrainSpur 0 wI0 sN t ∧ TSOErreichbar wI0 sN ∧
      sN.puffer 0 = [] ∧ sN.puffer 1 = [] ∧
      (∀ x ∈ t, FremdFrei x 0 vA) ∧
      (∀ x ∈ t, ∃ k' : Nat, k' ≤ 8 ∧
        x.puffer 0 = (wortEintraege vA zeugenWort).drop k') ∧
      read64 sN.mem vA = some zeugenWort ∧
      sN.mem.bytes vB = fByte ∧
      read64 sN.mem vB = some (BitVec.ofNat 64 7) ∧
      wI0.mem.bytes vA ≠ sN.mem.bytes vA ∧
      wI0.mem.bytes vB ≠ sN.mem.bytes vB ∧
      (issueByte wI1 1 vB fByte = some wI2 ∧
        flushKern wI2 1 = some wI3 ∧
        wI1 ∈ t ∧ wI2 ∈ t ∧ wI3 ∈ t) := by
  exact ⟨wI_trace, wI10, wI_spur, wI_erreichbar, wI_hempty, wI_hemptyF,
    wI_hstoer, wI_fifo, wI_liest_zurueck, wI_fremd_byte, wI_fremd_wort,
    wI_grp_aendert, wI_fremd_aendert,
    wI_issue, wI_fflush,
    by simp [wI_trace], by simp [wI_trace], by simp [wI_trace]⟩

/-- JOINT INHABITANT for `verflochten_liest_zurueck`: every premise
    holds jointly on the interleaved witness, with both memories
    changed. -/
theorem verflochten_liest_zurueck_zeuge :
    ∃ (s2 sN : TSOZustand) (t : List TSOZustand) (a : Adresse) (v : Wort),
      WortGruppe s2 0 a v ∧ lesbar8 s2.mem a = true ∧
      DrainSpur 0 s2 sN t ∧ sN ∈ t ∧ sN.puffer 0 = [] ∧
      (∀ x ∈ t, ∀ e ∈ x.puffer 1, e.addr ∉ Fuss a) ∧
      (∀ x ∈ t, ∀ d : Nat, d ≠ 0 → d ≠ 1 → x.puffer d = []) ∧
      read64 sN.mem a = some v ∧
      s2.mem.bytes a ≠ sN.mem.bytes a := by
  exact ⟨wI0, wI10, wI_trace, vA, zeugenWort, wI_hgrp, wI_hles,
    wI_spur, wI_hend, wI_hempty, wI_h1, wI_hRest,
    wI_liest_zurueck, wI_grp_aendert⟩

/-- JOINT INHABITANT for `verflochten_fremd_bleibt`: disjointness,
    footprint membership, a real own flush, preservation, and a real
    memory change one byte over. -/
theorem verflochten_fremd_bleibt_zeuge :
    ∃ (s s' : TSOZustand) (a b : Adresse) (k : Nat),
      Disjunkt a b ∧ k < 8 ∧
      (∀ e : TSOEintrag, e ∈ s.puffer 0 → e.addr ∈ Fuss a) ∧
      flushKern s 0 = some s' ∧
      s'.mem.bytes (addrOff b k) = s.mem.bytes (addrOff b k) ∧
      s.mem.bytes (addrOff a 1) ≠ s'.mem.bytes (addrOff a 1) := by
  refine ⟨wI3, wI4, vA, vB, 0, vA_vB_disjunkt, by decide,
    wI_own_in_fuss wI3 (by simp [wI_trace]), wI_e2, ?_, by decide⟩
  exact verflochten_fremd_bleibt wI3 wI4 vA vB vA_vB_disjunkt
    (wI_own_in_fuss wI3 (by simp [wI_trace])) wI_e2 0 (by decide)

/-- JOINT INHABITANT for `verflochten_fifo_suffix`: a mid-trace
    proper suffix plus a fully drained end. -/
theorem verflochten_fifo_suffix_zeuge :
    ∃ (s2 sN : TSOZustand) (t : List TSOZustand) (a : Adresse)
      (v : Wort) (x : TSOZustand),
      WortGruppe s2 0 a v ∧ DrainSpur 0 s2 sN t ∧
      (∀ y ∈ t, FremdFrei y 0 a) ∧ x ∈ t ∧
      (∃ k' : Nat, k' ≤ 8 ∧ x.puffer 0 = (wortEintraege a v).drop k') ∧
      x.puffer 0 ≠ wortEintraege a v ∧ sN.puffer 0 = [] := by
  refine ⟨wI0, wI10, wI_trace, vA, zeugenWort, wI3,
    wI_hgrp, wI_spur, wI_hstoer,
    by simp [wI_trace],
    wI_fifo wI3 (by simp [wI_trace]), by decide, wI_hempty⟩

/-! ## 10. Refusals: overlap fails the check, alignment is not enough. -/

/-- Overlapping foreign entry: core 1 holds byte 3 of the grouped
    footprint (the product of an overlapping foreign issue). -/
def wOv : TSOZustand :=
  ⟨wI1.mem, pufferSetze wI1.puffer 1 [⟨addrOff vA 3, fByte⟩]⟩

/-- The overlapping buffer content computes as written. -/
theorem wOv_p1 : wOv.puffer 1 = [⟨addrOff vA 3, fByte⟩] := by rfl

/-- OVERLAP REFUSED (decidable check): the finite list check fails
    on the overlapping entry, so no trace through this state can
    discharge `verflochten_liest_zurueck`. -/
theorem wOv_bool_verweigert : pufferFrei (wOv.puffer 1) vA = false := by
  decide

/-- OVERLAP REFUSED (proposition): the overlapping entry breaks
    foreign-footprint freedom. The same check gates both the
    overlapping issue's product and any flush from it. -/
theorem wOv_prop_verweigert : ¬ FremdFrei wOv 0 vA := by
  intro h
  have hmem : (⟨addrOff vA 3, fByte⟩ : TSOEintrag) ∈ wOv.puffer 1 := by
    rw [wOv_p1]
    simp
  have hfrei := h 1 (by decide) _ hmem
  exact hfrei (fuss_mem_offset vA 3 (by decide))

/-- ALIGNMENT ALONE IS NOT ENOUGH: `vA` is aligned, yet the
    overlapping state is no group — the structural exclusion check
    refuses what alignment admits. -/
theorem ausrichtung_allein_verweigert :
    ausgerichtet8 vA = true ∧ ¬ WortGruppe wOv 0 vA zeugenWort := by
  refine ⟨by decide, ?_⟩
  intro hgrp
  obtain ⟨_hbuf, hff⟩ := hgrp
  exact wOv_prop_verweigert hff

/-! ## 11. No hardware-atomicity claim; LOCK path stays disjoint. -/

/-- The first own flush visibly tears: byte 0 is new while byte 1
    still reads the pre-flush byte. Eight such visible steps are a
    software observation discipline, never a hardware-atomic
    instruction. -/
theorem verflochten_erster_schritt_reisst :
    wI1.mem.bytes (addrOff vA 0) = wortByte zeugenWort 0 ∧
    wI1.mem.bytes (addrOff vA 1) = wI0.mem.bytes (addrOff vA 1) := by
  have hbuf : wI0.puffer 0 =
      ⟨addrOff vA 0, wortByte zeugenWort 0⟩ ::
        (wortEintraege vA zeugenWort).drop 1 := by
    rfl
  exact ⟨flush_schreibt_kopf wI0 wI1 0 wI_e1 _ _ hbuf,
    flush_rahmen wI0 wI1 0 wI_e1 _ _ hbuf _
      (addrOff_ne8 (by decide) (by decide) (by decide))⟩

/-- LOCK stays disjoint on the interleaved start: the grouped buffer
    is nonempty, so no LOCK source refinement is claimed or needed. -/
theorem verflochten_verweigert_lock (delta : Wort) :
    lockSchritt (.xadd64 vA delta) 0 wI0 = none :=
  gruppe_verweigert_lock wI0 0 vA zeugenWort delta wI_hgrp

/- CUTS:
    - Proved here: whole-word grouping across a drain trace with REAL
      interleaved foreign accesses. `verflochten_liest_zurueck`
      (generic read-back with exclusion from finite per-state list
      checks `wI_h1`/`wI_hRest`, never assumed end-state equality);
      `verflochten_fifo_suffix` (own FIFO retained as suffixes of the
      canonical eight-entry list); `verflochten_fremd_bleibt` plus
      `verflochten_fremd_installiert` (foreign disjoint writes
      installed by their own flush and preserved across own flushes);
      `wI_zeuge_gelenk` (joint reached memory-changing witness with
      an actual foreign issue AND foreign flush between own flushes,
      both buffers drained, both words reading back); per-claim
      joint inhabitants; overlapping issue/flush refusal (bool and
      Prop); alignment-only counterexample; first-step tearing
      (no hardware-atomicity claim); LOCK refusal on grouped states.
    - NOT proved here, and not claimed:
      - No multi-byte hardware atomicity: the drain passes through
        ten visible intermediate states; grouping is a software
        observation discipline, not a silicon guarantee.
      - No source correspondence: nothing links Gabbro source, IR,
        checker verdicts or contracts to these traces; no entry,
        ABI, loader, relocation, image-layout or cost claim.
      - No per-access W/GX simulation and no typed-carrier bridge:
        consumers CarrierTraceBridge650, BridgeWrite and BridgeRead
        own that; this module hands them `verflochten_liest_zurueck`
        (read-back), `verflochten_fifo_suffix` (FIFO shape),
        `verflochten_fremd_bleibt`/`verflochten_fremd_installiert`
        (foreign-write facts), `eintragFrei`/`pufferFrei` plus
        `pufferFrei_gilt`/`fremdFrei_von_pruefung`/
        `spurFrei_von_pruefung` (finite-check exclusion API),
        `wI_spur`/`wI_erreichbar`/`wI_zeuge_gelenk` (trace facts)
        and the three `_zeuge` inhabitants.
      - No fairness, progress, timing or liveness claim; no
        interrupt, device, MMIO or DMA model; no LOCK source
        refinement (`verflochten_verweigert_lock` keeps the LOCK
        path disjoint; WordAtomicity owns it).
      - Two-core slice only: exclusion is checked on core 1 with
        every other foreign core empty (`wI_hRest`); wider core
        counts need the same checks per core.
      - Axioms stay within the standard goal set
        (propext, Classical.choice, Quot.sound).
-/

#print axioms eintragFrei
#print axioms pufferFrei
#print axioms eintragFrei_gilt
#print axioms pufferFrei_gilt
#print axioms fremdFrei_von_pruefung
#print axioms spurFrei_von_pruefung
#print axioms verflochten_liest_zurueck
#print axioms verflochten_fifo_suffix
#print axioms worteintrag_in_fuss
#print axioms suffix_eintrag_in_fuss
#print axioms verflochten_fremd_bleibt
#print axioms verflochten_fremd_installiert
#print axioms wI_e1
#print axioms wI_issue
#print axioms wI_fflush
#print axioms wI_e8
#print axioms vB_ausserhalb
#print axioms vA_vB_disjunkt
#print axioms wI_hgrp
#print axioms wI_hles
#print axioms wI_spur
#print axioms wI_hend
#print axioms wI_hempty
#print axioms wI_liest_zurueck
#print axioms wI_fifo
#print axioms wI_fremd_byte
#print axioms wI_fremd_wort
#print axioms wI_zeuge_gelenk
#print axioms verflochten_liest_zurueck_zeuge
#print axioms verflochten_fremd_bleibt_zeuge
#print axioms verflochten_fifo_suffix_zeuge
#print axioms wOv_bool_verweigert
#print axioms wOv_prop_verweigert
#print axioms ausrichtung_allein_verweigert
#print axioms verflochten_erster_schritt_reisst
#print axioms verflochten_verweigert_lock

end Gabbro.Grammatik.X86
