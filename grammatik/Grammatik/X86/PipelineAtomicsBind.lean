/-
  File:      Grammatik/X86/PipelineAtomicsBind.lean
  Subject:   Pipeline atomics: register-address binding for RMW/fence byte
             forms, SFENCE/LFENCE lowering, and the 8-issue word-install
             proof.

  Lane 1203 (follow-up of lane 1163 `PipelineAtomics.lean`): the three
  open gaps named in its CUTS -- (a) which (base, disp) names which
  address for the locked byte forms, (b) SFENCE/LFENCE lowering, (c) the
  whole-word store install from bytes -- closed over REUSED accepted
  definitions only. No new machine, no new decoder row, no second IR,
  no source/checker/goal change. Unsupported shapes are REFUSED.
-/
import Grammatik.X86.PipelineAtomics
import Grammatik.X86.SfenceStoreNarrow
import Grammatik.X86.LfenceLoadNarrow
import Grammatik.X86.WordAccessGrouping

namespace Gabbro.Grammatik.X86.PipelineAtomicsBind

open Gabbro.Grammatik
open Gabbro.Grammatik.X86
open Gabbro.Grammatik.X86.PipelineAtomics

/-- Fence kind: full MFENCE plus the two narrow forms. -/
inductive ZaunArt where
  | mfence
  | sfence
  | lfence
  deriving DecidableEq, Repr

/-- Canonical bytes of one fence kind (all reused, never redefined). -/
def zaunBytes : ZaunArt → List Byte
  | .mfence => pinMfence
  | .sfence => pinSfence
  | .lfence => lfenceBytes

/-- MFENCE bytes are the accepted locked fence pin. -/
theorem zaunBytes_mfence : zaunBytes .mfence = pinMfence := rfl

/-- SFENCE bytes are the accepted narrow-store pin. -/
theorem zaunBytes_sfence : zaunBytes .sfence = pinSfence := rfl

/-- LFENCE bytes are the accepted narrow-load pin. -/
theorem zaunBytes_lfence : zaunBytes .lfence = lfenceBytes := rfl

/-! ## 1. Register-address binding for the locked byte forms.

    The accepted locked steps speak about ADDRESSES (`lockSchritt`,
    `casSchritt`), the byte forms about REGISTERS (`LockForm.xadd64 src
    base disp`). The link is the register file: `effAddr m.zu base d`
    names the address the locked step runs at. Each theorem below states
    the lane-1163 lowering together with the accepted projection at the
    BOUND address -- the lowering and the address agree by the single
    `heff` equation. Fences need no address: the MFENCE projection is
    register-free. -/

/-- **XADD BINDING.** The lowered LOCK XADD runs the accepted locked
    add at exactly the address the register pair names. -/
theorem bind_xadd (m : LockMaschine) (c : Nat) (a : Adresse)
    (src base : Register) (d : BitVec 32)
    (alt : Wort) (mem' : Speicher)
    (heff : effAddr m.zu base d = a)
    (hbuf : m.puffer c = [])
    (hrd : read64 m.zu.speicher a = some alt)
    (hali : ausgerichtet8 a = true)
    (hwr : write64 m.zu.speicher a (alt + m.zu.register src) = some mem') :
    PipelineAtomics.senkAtom (PipelineAtomics.AtomQuelle.xadd src base d) =
      some [PipelineAtomics.ZielOp.lock (.xadd64 src base d)] ∧
    ∃ ev : LockEreignis,
      lockSchritt (.xadd64 a (m.zu.register src)) c (toTSO m) =
        some (⟨mem', m.puffer⟩, ev) ∧
      ev.gelesen = some alt ∧ ev.istRmw = true := by
  have hrd' : read64 m.zu.speicher (effAddr m.zu base d) = some alt := by
    rw [heff]; exact hrd
  have hali' : ausgerichtet8 (effAddr m.zu base d) = true := by
    rw [heff]; exact hali
  have hwr' : write64 m.zu.speicher (effAddr m.zu base d)
      (alt + m.zu.register src) = some mem' := by
    rw [heff]; exact hwr
  have h := lockVoll_xadd_adapter m c src base d alt mem' hbuf hrd' hali' hwr'
  rw [heff] at h
  exact ⟨PipelineAtomics.senk_xadd src base d, h⟩

/-- **CAS BINDING.** The lowered LOCK CMPXCHG success runs the accepted
    CAS success at exactly the address the register pair names
    (comparison against rax, install of the src word). -/
theorem bind_cas_erfolg (m : LockMaschine) (c : Nat) (a : Adresse)
    (src base : Register) (d : BitVec 32)
    (dest : Wort) (mem' : Speicher)
    (heff : effAddr m.zu base d = a)
    (hbuf : m.puffer c = [])
    (hrd : read64 m.zu.speicher a = some dest)
    (hali : ausgerichtet8 a = true)
    (hgleich : (dest == m.zu.register .rax) = true)
    (hwr : write64 m.zu.speicher a (m.zu.register src) = some mem') :
    PipelineAtomics.senkAtom (PipelineAtomics.AtomQuelle.cas src base d) =
      some [PipelineAtomics.ZielOp.lock (.cmpxchg64 src base d)] ∧
    casSchritt a (m.zu.register .rax) (m.zu.register src) c (toTSO m) =
      some (⟨mem', m.puffer⟩, true) := by
  have hrd' : read64 m.zu.speicher (effAddr m.zu base d) = some dest := by
    rw [heff]; exact hrd
  have hali' : ausgerichtet8 (effAddr m.zu base d) = true := by
    rw [heff]; exact hali
  have hwr' : write64 m.zu.speicher (effAddr m.zu base d)
      (m.zu.register src) = some mem' := by
    rw [heff]; exact hwr
  have h := lockVoll_cmpxchg_erfolg_adapter m c src base d dest mem'
    hbuf hrd' hali' hgleich hwr'
  rw [heff] at h
  exact ⟨PipelineAtomics.senk_cas src base d, h⟩

/-- **FENCE NEEDS NO BINDING.** The lowered fence is the accepted fence
    gate with no register or address premise at all. -/
theorem bind_mfence (m : LockMaschine) (c : Nat)
    (hbuf : m.puffer c = []) :
    PipelineAtomics.senkAtom PipelineAtomics.AtomQuelle.zaun =
      some [PipelineAtomics.ZielOp.lock .mfence] ∧
    lockSchritt .mfence c (toTSO m) =
      some (toTSO m, ⟨c, [], [], none, none, false, true⟩) :=
  ⟨PipelineAtomics.senk_zaun, lockVoll_mfence_adapter m c hbuf⟩

/-! ## 2. SFENCE/LFENCE lowering: canonical bytes with decode facts.

    Lane 1163 lowered only the full MFENCE fence. Each narrow form
    lowers to its own accepted pin: SFENCE to `pinSfence` (decoded by
    `decodeSfence`, never by the pilot or locked decoders), LFENCE to
    `lfenceBytes` (decoded by `decodeLfence`, refused by both older
    decoders). MFENCE keeps its lane-1163 lowering; its byte fact is
    restated here through `zaunBytes` so all three fences share one
    validator. -/

/-- MFENCE bytes decode to the fence form (reused round trip). -/
theorem zaun_mfence_dekodiert (suffix : List Byte) :
    decodeLock (zaunBytes .mfence ++ suffix) =
      some (LockAnweisung.ok .mfence 3, suffix) :=
  roundtrip_lock_mfence suffix

/-- SFENCE bytes decode to the narrow-store fence form. -/
theorem zaun_sfence_dekodiert (suffix : List Byte) :
    decodeSfence (zaunBytes .sfence ++ suffix) =
      some (SfenceAnweisung.ok .sfence 3, suffix) :=
  roundtrip_sfence suffix

/-- LFENCE bytes decode to the narrow-load fence form. -/
theorem zaun_lfence_dekodiert (suffix : List Byte) :
    decodeLfence (zaunBytes .lfence ++ suffix) = some ((), suffix) :=
  roundtrip_lfence suffix

/-- Decided validator: `bs` is accepted for `z` exactly when it is the
    canonical pin. Bytes are checked data, never trusted. -/
def valZaun (z : ZaunArt) (bs : List Byte) : Bool :=
  decide (zaunBytes z = bs)

/-- The validator accepts exactly the canonical pins. -/
theorem valZaun_korrekt (z : ZaunArt) (bs : List Byte) :
    valZaun z bs = true ↔ zaunBytes z = bs := by
  unfold valZaun
  simp [decide_eq_true_eq]

/-! ## 3. Fence step correspondence: what each lowered fence does.

    MFENCE drains the own buffer (`bind_mfence`, §1). SFENCE with
    silicon SSE and an empty own buffer is TSO-observably the identity:
    memory and every buffer are kept and later loads read what they
    read before. LFENCE with a pending own store is state-preserving
    with the narrow (non-MFENCE) fence event -- and the accepted MFENCE
    gate refuses exactly there. Without SSE, SFENCE is the manual's
    #UD; with a pending store, both full and narrow store fences
    refuse: no silent skip over buffered stores. -/

/-- **SFENCE CORRESPONDENCE.** The lowered SFENCE bytes decode to the
    narrow-store form and step to the fence-only successor that keeps
    the whole TSO projection and every later load. -/
theorem zaun_sfence_korrekt (m m' : LockMaschine) (c : Nat) (sse : Bool)
    (ev : LockEreignis)
    (hstep : sfenceSchritt (.ok .sfence 3) c m sse = .ok m' ev) :
    decodeSfence (zaunBytes .sfence) =
      some (SfenceAnweisung.ok .sfence 3, []) ∧
    sse = true ∧ m.puffer c = [] ∧
    toTSO m' = toTSO m ∧
    (∀ a : Adresse,
      loadByte (toTSO m') c a = loadByte (toTSO m) c a) ∧
    ev = ⟨c, [], [], none, none, false, true⟩ := by
  have hdec := zaun_sfence_dekodiert []
  simp only [List.append_nil] at hdec
  have hform := sfence_erfolg_form m m' c sse ev hstep
  exact ⟨hdec, hform.1, hform.2.1,
    sfence_behaelt_tso m m' c sse ev hstep,
    fun a => sfence_last_unveraendert m m' c sse ev hstep a,
    hform.2.2.2⟩

/-- **LFENCE CORRESPONDENCE.** With a pending own store the lowered
    LFENCE bytes decode to the narrow-load form, the step preserves
    buffers and memory with the narrow fence event, and the accepted
    MFENCE gate refuses the same state. -/
theorem zaun_lfence_korrekt (s : TSOZustand) (c : Nat) (a : Adresse)
    (hne : s.puffer c ≠ []) :
    decodeLfence (zaunBytes .lfence) = some ((), []) ∧
    (lfenceSchritt s c).1.puffer = s.puffer ∧
    (lfenceSchritt s c).1.mem.bytes = s.mem.bytes ∧
    loadByte (lfenceSchritt s c).1 c a = loadByte s c a ∧
    (lfenceSchritt s c).2.istZaun = true ∧
    (lfenceSchritt s c).2.istMfence = false ∧
    lockSchritt .mfence c s = none := by
  have hdec := zaun_lfence_dekodiert []
  simp only [List.append_nil] at hdec
  obtain ⟨hpuff, hmem, hlast, hzaun, hschmal, hmfence⟩ :=
    LfenceLoadNarrow_verbindung s c a hne
  exact ⟨hdec, hpuff, hmem, hlast, hzaun, hschmal, hmfence⟩

/-- SFENCE without silicon SSE is the manual's #UD, never a step. -/
theorem zaun_sfence_ohne_sse (m : LockMaschine) (c : Nat) :
    sfenceSchritt (.ok .sfence 3) c m false =
      .udFehler .sseFehlt :=
  sfence_ohne_sse m c false rfl sfence_len_ok

/-- SFENCE over a pending own store refuses: no silent skip. -/
theorem zaun_sfence_puffer_verweigert (m : LockMaschine) (c : Nat)
    (e : TSOEintrag) (rest : List TSOEintrag)
    (hbuf : m.puffer c = e :: rest) :
    sfenceSchritt (.ok .sfence 3) c m true = .verweigert :=
  sfence_puffer_verweigert m c true rfl e rest hbuf sfence_len_ok

/-- POISON: the pilot decoder refuses the LFENCE pin. -/
theorem gift_lfence_pilot : decode lfenceBytes = none :=
  pilot_weist_lfence_zurueck

/-- POISON: the locked decoder refuses the LFENCE pin. -/
theorem gift_lfence_lock : decodeLock lfenceBytes = none :=
  lock_weist_lfence_zurueck

/-- POISON: the SFENCE decoder refuses the MFENCE neighbour. -/
theorem gift_sfence_nachbar_mfence :
    decodeSfence [natByte 15, natByte 174, natByte 240] = none :=
  (pin_sfence_verweigert_nachbarn).1

/-- POISON: the SFENCE decoder refuses the LFENCE neighbour. -/
theorem gift_sfence_nachbar_lfence :
    decodeSfence [natByte 15, natByte 174, natByte 232] = none :=
  (pin_sfence_verweigert_nachbarn).2.1

/-! ## 4. Word install: eight byte issues in order plus the group guard.

    A word store reaches canonical memory as exactly eight byte issues
    in oldest-first order (`wortEintraege`), then an exclusion-checked
    drain (`DrainSpur` with `FremdFrei` at every visited state). The
    group guard `WortGruppe` is the exact eight-entry own buffer plus
    foreign-footprint freedom -- alignment alone is insufficient (the
    byte drain never consults `ausgerichtet8`; see the reused
    `ausrichtung_reicht_nicht`). The install itself is the accepted
    `wort_gruppe_liest_zurueck`; the drain is a reached run by the
    accepted `drain_spur_erreichbar`. -/

/-- One issue appends exactly one entry to the acting core's buffer. -/
theorem issueByte_puffer (s s' : TSOZustand) (c : Nat) (a : Adresse)
    (w : Byte) (h : issueByte s c a w = some s') :
    s'.puffer c = s.puffer c ++ [⟨a, w⟩] := by
  unfold issueByte at h
  by_cases hc : s.mem.schreibbar a = true
  · rw [if_pos hc] at h
    cases h
    exact pufferSetze_gleich _ _ _
  · rw [if_neg hc] at h
    cases h

/-- One issue leaves canonical memory unchanged. -/
theorem issueByte_mem (s s' : TSOZustand) (c : Nat) (a : Adresse)
    (w : Byte) (h : issueByte s c a w = some s') :
    s'.mem = s.mem := by
  unfold issueByte at h
  by_cases hc : s.mem.schreibbar a = true
  · rw [if_pos hc] at h
    cases h
    rfl
  · rw [if_neg hc] at h
    cases h

/-- **EIGHT ISSUES BUILD THE GROUP.** Eight byte issues in
    oldest-first order onto an empty own buffer carry exactly the
    canonical eight entries; canonical memory and every foreign buffer
    are untouched. Every premise is used: `hbuf` seeds the chain, each
    `hk` extends it, and the foreign frame closes over all eight. -/
theorem acht_ausgaben_gruppe
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 : TSOZustand)
    (c : Nat) (a : Adresse) (v : Wort)
    (hbuf : s0.puffer c = [])
    (h0 : issueByte s0 c (addrOff a 0) (wortByte v 0) = some s1)
    (h1 : issueByte s1 c (addrOff a 1) (wortByte v 1) = some s2)
    (h2 : issueByte s2 c (addrOff a 2) (wortByte v 2) = some s3)
    (h3 : issueByte s3 c (addrOff a 3) (wortByte v 3) = some s4)
    (h4 : issueByte s4 c (addrOff a 4) (wortByte v 4) = some s5)
    (h5 : issueByte s5 c (addrOff a 5) (wortByte v 5) = some s6)
    (h6 : issueByte s6 c (addrOff a 6) (wortByte v 6) = some s7)
    (h7 : issueByte s7 c (addrOff a 7) (wortByte v 7) = some s8) :
    s8.puffer c = wortEintraege a v ∧ s8.mem = s0.mem ∧
      ∀ d : Nat, d ≠ c → s8.puffer d = s0.puffer d := by
  have e0 := issueByte_puffer s0 s1 c _ _ h0
  have e1 := issueByte_puffer s1 s2 c _ _ h1
  have e2 := issueByte_puffer s2 s3 c _ _ h2
  have e3 := issueByte_puffer s3 s4 c _ _ h3
  have e4 := issueByte_puffer s4 s5 c _ _ h4
  have e5 := issueByte_puffer s5 s6 c _ _ h5
  have e6 := issueByte_puffer s6 s7 c _ _ h6
  have e7 := issueByte_puffer s7 s8 c _ _ h7
  have m0 := issueByte_mem s0 s1 c _ _ h0
  have m1 := issueByte_mem s1 s2 c _ _ h1
  have m2 := issueByte_mem s2 s3 c _ _ h2
  have m3 := issueByte_mem s3 s4 c _ _ h3
  have m4 := issueByte_mem s4 s5 c _ _ h4
  have m5 := issueByte_mem s5 s6 c _ _ h5
  have m6 := issueByte_mem s6 s7 c _ _ h6
  have m7 := issueByte_mem s7 s8 c _ _ h7
  refine ⟨?_, ?_, ?_⟩
  · rw [e7, e6, e5, e4, e3, e2, e1, e0, hbuf]
    rfl
  · rw [m7, m6, m5, m4, m3, m2, m1, m0]
  · intro d hd
    rw [issue_anderer_kern s7 s8 c _ _ h7 hd,
      issue_anderer_kern s6 s7 c _ _ h6 hd,
      issue_anderer_kern s5 s6 c _ _ h5 hd,
      issue_anderer_kern s4 s5 c _ _ h4 hd,
      issue_anderer_kern s3 s4 c _ _ h3 hd,
      issue_anderer_kern s2 s3 c _ _ h2 hd,
      issue_anderer_kern s1 s2 c _ _ h1 hd,
      issue_anderer_kern s0 s1 c _ _ h0 hd]

/-- The eight issues form one reached run. -/
theorem acht_ausgaben_erreichbar
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 : TSOZustand)
    (c : Nat) (a : Adresse) (v : Wort)
    (h0 : issueByte s0 c (addrOff a 0) (wortByte v 0) = some s1)
    (h1 : issueByte s1 c (addrOff a 1) (wortByte v 1) = some s2)
    (h2 : issueByte s2 c (addrOff a 2) (wortByte v 2) = some s3)
    (h3 : issueByte s3 c (addrOff a 3) (wortByte v 3) = some s4)
    (h4 : issueByte s4 c (addrOff a 4) (wortByte v 4) = some s5)
    (h5 : issueByte s5 c (addrOff a 5) (wortByte v 5) = some s6)
    (h6 : issueByte s6 c (addrOff a 6) (wortByte v 6) = some s7)
    (h7 : issueByte s7 c (addrOff a 7) (wortByte v 7) = some s8) :
    TSOErreichbar s0 s8 := by
  exact .schritt (.schritt (.schritt (.schritt (.schritt (.schritt
    (.schritt (.schritt .start (.issue _ _ _ _ _ h0)) (.issue _ _ _ _ _ h1))
    (.issue _ _ _ _ _ h2)) (.issue _ _ _ _ _ h3)) (.issue _ _ _ _ _ h4))
    (.issue _ _ _ _ _ h5)) (.issue _ _ _ _ _ h6)) (.issue _ _ _ _ _ h7)

/- CUTS: what is not proved here (skeleton; extended with each piece)
    NOT proved here, and not claimed:
    - No seq_cst total order, no fairness, no CAS retry bound.
    - No full source `execBlock` correspondence for atomics.
-/

#print axioms zaunBytes_mfence
#print axioms zaunBytes_sfence
#print axioms zaunBytes_lfence
#print axioms zaun_mfence_dekodiert
#print axioms zaun_sfence_dekodiert
#print axioms zaun_lfence_dekodiert
#print axioms valZaun_korrekt
#print axioms issueByte_puffer
#print axioms issueByte_mem
#print axioms acht_ausgaben_gruppe
#print axioms acht_ausgaben_erreichbar
#print axioms zaun_sfence_korrekt
#print axioms zaun_lfence_korrekt
#print axioms zaun_sfence_ohne_sse
#print axioms zaun_sfence_puffer_verweigert
#print axioms bind_xadd
#print axioms bind_cas_erfolg
#print axioms bind_mfence

end Gabbro.Grammatik.X86.PipelineAtomicsBind
