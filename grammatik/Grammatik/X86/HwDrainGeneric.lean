/-
  File:      Grammatik/X86/HwDrainGeneric.lean
  Subject:   Generic drain-equals-write64 induction on the coherent machine
             (lane 1207, follow-up of lane 1185 `HwForwardingGeneric`).

  Lifts the accepted word drain (`DrainSpur`, `WortGruppe`, `FremdFrei`,
  `flushKern`, `wortEintraege`) to a generic induction: draining the
  eight buffered entries of a word store, in any interleaving with
  foreign flushes/issues satisfying `FremdFrei`, installs exactly the
  `write64` footprint bytes, with the visited states exactly the stated
  prefixes. A foreign overlapping flush breaks it (counter-witness).
  No model is redefined here.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Speicher
import Grammatik.X86.TSO
import Grammatik.X86.WordAccessGrouping
import Grammatik.X86.HwStackCalls
import Grammatik.X86.HwForwardingGeneric
import Grammatik.X86.HardwareExecution

namespace Gabbro.Grammatik.X86

/-! ## 1. Family events and the adapter. -/

/-- Generic drain family events on the coherent machine. -/
inductive DrainEreignis where
  | speichere : Adresse → Wort → DrainEreignis
  | eigenSpuele : DrainEreignis
  | fremdSpuele : Nat → DrainEreignis
  | fremdAusgabe : Nat → TSOEintrag → DrainEreignis
  | beobachte : Adresse → DrainEreignis
  deriving DecidableEq, Repr

/-- The family adapter: word stores buffer, drains flush, observations
    read without moving state. -/
def drainAdapter : HwAdapter DrainEreignis :=
  ⟨fun m c ev => match ev with
    | .speichere a v => hwWortAusgabe m c a v
    | .eigenSpuele =>
      match flushKern (tsoAnsicht m) c with
      | some s' => some (setTso m s')
      | none => none
    | .fremdSpuele d =>
      match flushKern (tsoAnsicht m) d with
      | some s' => some (setTso m s')
      | none => none
    | .fremdAusgabe d e =>
      match issueByte (tsoAnsicht m) d e.addr e.wert with
      | some s' => some (setTso m s')
      | none => none
    | .beobachte a =>
      match stapelLadeWort (tsoAnsicht m) c a with
      | some _ => some m
      | none => none⟩

/-! ## 2. Adapter duties: well-formedness, agreement, embedding. -/

/-- Every adapter step preserves well-formedness: stores, flushes and
    issues ride `setTso`, observations are silent. -/
theorem drainAdapter_wf (m : HwMaschine) (c : Nat) (ev : DrainEreignis)
    (m' : HwMaschine) (h : drainAdapter.schritt m c ev = some m')
    (hwf : HwWf m) : HwWf m' := by
  cases ev with
  | speichere a v =>
    have had : drainAdapter.schritt m c (.speichere a v) =
        hwWortAusgabe m c a v := rfl
    rw [had] at h
    unfold hwWortAusgabe at h
    cases h1 : issueListe (tsoAnsicht m) c (wortEintraege a v) with
    | none => rw [h1] at h; cases h
    | some s' => rw [h1] at h; cases h; exact setTso_wf _ s' hwf
  | eigenSpuele =>
    cases hfl : flushKern (tsoAnsicht m) c with
    | none =>
      have hh : drainAdapter.schritt m c .eigenSpuele = none := by
        show (match flushKern (tsoAnsicht m) c with
          | some s' => some (setTso m s') | none => none) = none
        rw [hfl]
      rw [hh] at h; cases h
    | some s' =>
      have hh : drainAdapter.schritt m c .eigenSpuele =
          some (setTso m s') := by
        show (match flushKern (tsoAnsicht m) c with
          | some s' => some (setTso m s') | none => none) = _
        rw [hfl]
      rw [hh] at h; cases h; exact setTso_wf _ s' hwf
  | fremdSpuele d =>
    cases hfl : flushKern (tsoAnsicht m) d with
    | none =>
      have hh : drainAdapter.schritt m c (.fremdSpuele d) = none := by
        show (match flushKern (tsoAnsicht m) d with
          | some s' => some (setTso m s') | none => none) = none
        rw [hfl]
      rw [hh] at h; cases h
    | some s' =>
      have hh : drainAdapter.schritt m c (.fremdSpuele d) =
          some (setTso m s') := by
        show (match flushKern (tsoAnsicht m) d with
          | some s' => some (setTso m s') | none => none) = _
        rw [hfl]
      rw [hh] at h; cases h; exact setTso_wf _ s' hwf
  | fremdAusgabe d e =>
    cases hfl : issueByte (tsoAnsicht m) d e.addr e.wert with
    | none =>
      have hh : drainAdapter.schritt m c (.fremdAusgabe d e) = none := by
        show (match issueByte (tsoAnsicht m) d e.addr e.wert with
          | some s' => some (setTso m s') | none => none) = none
        rw [hfl]
      rw [hh] at h; cases h
    | some s' =>
      have hh : drainAdapter.schritt m c (.fremdAusgabe d e) =
          some (setTso m s') := by
        show (match issueByte (tsoAnsicht m) d e.addr e.wert with
          | some s' => some (setTso m s') | none => none) = _
        rw [hfl]
      rw [hh] at h; cases h; exact setTso_wf _ s' hwf
  | beobachte a =>
    cases hl : stapelLadeWort (tsoAnsicht m) c a with
    | none =>
      have hh : drainAdapter.schritt m c (.beobachte a) = none := by
        show (match stapelLadeWort (tsoAnsicht m) c a with
          | some _ => some m | none => none) = none
        rw [hl]
      rw [hh] at h; cases h
    | some w =>
      have hh : drainAdapter.schritt m c (.beobachte a) = some m := by
        show (match stapelLadeWort (tsoAnsicht m) c a with
          | some _ => some m | none => none) = some m
        rw [hl]
      rw [hh] at h; cases h; exact hwf

/-- A buffered word store appends exactly the canonical eight entries. -/
theorem drainSpeichere_puffer (m : HwMaschine) (c : Nat)
    (a : Adresse) (v : Wort) (m' : HwMaschine)
    (h : drainAdapter.schritt m c (.speichere a v) = some m') :
    m'.puffer c = m.puffer c ++ wortEintraege a v :=
  hwWortAusgabe_puffer m c a v m' h

/-- A buffered word store changes no shared-memory byte. -/
theorem drainSpeichere_kein_speicher (m : HwMaschine) (c : Nat)
    (a : Adresse) (v : Wort) (m' : HwMaschine)
    (h : drainAdapter.schritt m c (.speichere a v) = some m')
    (x : Adresse) :
    m'.mem.bytes x = m.mem.bytes x :=
  hwWortAusgabe_kein_speicher m c a v m' h x

/-- An own-drain adapter step IS the accepted oldest-entry flush. -/
theorem drainEigen_ist_flush (m : HwMaschine) (c : Nat)
    (s' : TSOZustand)
    (hfl : flushKern (tsoAnsicht m) c = some s') (m' : HwMaschine)
    (h : drainAdapter.schritt m c .eigenSpuele = some m') :
    m' = setTso m s' := by
  have hh : drainAdapter.schritt m c .eigenSpuele =
      some (setTso m s') := by
    show (match flushKern (tsoAnsicht m) c with
      | some s' => some (setTso m s') | none => none) = _
    rw [hfl]
  rw [hh] at h
  exact (Option.some.inj h).symm

/-- An own-drain adapter step is a machine flush event. -/
theorem drainEigen_ist_schritt (m : HwMaschine) (c : Nat)
    (s' : TSOZustand) (e : TSOEintrag)
    (hfl : flushKern (tsoAnsicht m) c = some s')
    (hkopf : (m.puffer c).head? = some e) :
    HwSchritt m (setTso m s') (.spülung c e) :=
  .spüle c e s' hfl hkopf

/-- A successful observation moves no state. -/
theorem drainBeobachte_still (m : HwMaschine) (c : Nat) (a : Adresse)
    (w : Wort) (h : stapelLadeWort (tsoAnsicht m) c a = some w) :
    drainAdapter.schritt m c (.beobachte a) = some m := by
  show (match stapelLadeWort (tsoAnsicht m) c a with
    | some _ => some m | none => none) = _
  rw [h]

/-- EMPTY DRAIN REFUSES: flushing an empty own buffer admits no step. -/
theorem drainEigen_leer_verweigert (m : HwMaschine) (c : Nat)
    (hleer : m.puffer c = []) :
    drainAdapter.schritt m c .eigenSpuele = none := by
  have hfl : flushKern (tsoAnsicht m) c = none := by
    apply flush_leer
    simpa [tsoAnsicht] using hleer
  show (match flushKern (tsoAnsicht m) c with
    | some s' => some (setTso m s') | none => none) = none
  rw [hfl]

/-- GUARD STORE REFUSES: without write permission at the first byte
    the whole word fold refuses. -/
theorem drainSpeichere_wache (m : HwMaschine) (c : Nat)
    (a : Adresse) (v : Wort)
    (hguard : m.mem.schreibbar (addrOff a 0) = false) :
    drainAdapter.schritt m c (.speichere a v) = none := by
  have had : drainAdapter.schritt m c (.speichere a v) =
      hwWortAusgabe m c a v := rfl
  rw [had]
  unfold hwWortAusgabe
  have hfirst : issueByte (tsoAnsicht m) c (addrOff a 0)
      (wortByte v 0) = none :=
    issue_verweigert _ _ _ _
      (by simpa [addrOff_null, tsoAnsicht_speicher] using hguard)
  have hcons : wortEintraege a v =
      ⟨addrOff a 0, wortByte v 0⟩ ::
      [⟨addrOff a 1, wortByte v 1⟩,
       ⟨addrOff a 2, wortByte v 2⟩,
       ⟨addrOff a 3, wortByte v 3⟩,
       ⟨addrOff a 4, wortByte v 4⟩,
       ⟨addrOff a 5, wortByte v 5⟩,
       ⟨addrOff a 6, wortByte v 6⟩,
       ⟨addrOff a 7, wortByte v 7⟩] := rfl
  have hfold : issueListe (tsoAnsicht m) c
      (⟨addrOff a 0, wortByte v 0⟩ ::
      [⟨addrOff a 1, wortByte v 1⟩,
       ⟨addrOff a 2, wortByte v 2⟩,
       ⟨addrOff a 3, wortByte v 3⟩,
       ⟨addrOff a 4, wortByte v 4⟩,
       ⟨addrOff a 5, wortByte v 5⟩,
       ⟨addrOff a 6, wortByte v 6⟩,
       ⟨addrOff a 7, wortByte v 7⟩]) = none :=
    issueListe_cons_none _ _ _ _ hfirst
  rw [hcons, hfold]

/-- DARK OBSERVATION REFUSES: without read permission at the first
    byte the whole word observation refuses. -/
theorem drainBeobachte_dunkel (s : TSOZustand) (c : Nat) (a : Adresse)
    (hguard : s.mem.lesbar (addrOff a 0) = false) :
    stapelLadeWort s c a = none :=
  stapelPop_unlesbar s c a hguard

/-! ## 3. Generic prefixes: visited states are stated prefixes. -/

/-- INTERMEDIATE PREFIX (generic): every visited state carries a
    suffix of the canonical eight-entry list with the installed
    prefix in memory. The group pins the start buffer, the trace the
    prefix, the exclusion every foreign step, membership the state. -/
theorem drainZwischen_praefix (c : Nat) (a : Adresse) (v : Wort)
    (s sN : TSOZustand) (t : List TSOZustand)
    (hgrp : WortGruppe s c a v)
    (hspur : DrainSpur c s sN t)
    (hstoer : ∀ x ∈ t, FremdFrei x c a)
    (x : TSOZustand) (hx : x ∈ t) :
    ∃ k' : Nat, k' ≤ 8 ∧
      x.puffer c = (wortEintraege a v).drop k' ∧
      (∀ j : Nat, j < k' → x.mem.bytes (addrOff a j) = wortByte v j) := by
  obtain ⟨hbufl, _hff⟩ := hgrp
  have hbase : s.puffer c = (wortEintraege a v).drop 0 := by
    rw [hbufl]
    rfl
  obtain ⟨k', _hk0, hk'8, hbufN, hmemN⟩ :=
    drain_installiert_aux c a v s sN t hspur hstoer 0 (Nat.zero_le 8)
      hbase (fun j hj => absurd hj (by omega)) x hx
  exact ⟨k', hk'8, hbufN, hmemN⟩

/-- UNINSTALLED PREFIX PRESERVED (generic): from `k` installed bytes
    the not-yet-drained footprint bytes still read the start memory.
    The trace, the exclusion check and the buffer shape feed every
    step; own flushes install a different byte (`addrOff_ne8`),
    foreign flushes avoid the footprint, foreign issues are silent. -/
theorem drainUninstalliert_bleibt_aux (c : Nat) (a : Adresse) (v : Wort)
    (s sN : TSOZustand) (t : List TSOZustand)
    (hspur : DrainSpur c s sN t) :
    ∀ (hstoer : ∀ x ∈ t, FremdFrei x c a) (k : Nat), k ≤ 8 →
      ∀ (hbuf : s.puffer c = (wortEintraege a v).drop k)
        (x : TSOZustand), x ∈ t →
        ∃ k' : Nat, k ≤ k' ∧ k' ≤ 8 ∧
          x.puffer c = (wortEintraege a v).drop k' ∧
          (∀ j : Nat, k' ≤ j → j < 8 →
            x.mem.bytes (addrOff a j) = s.mem.bytes (addrOff a j)) := by
  induction hspur with
  | leer s =>
    intro hstoer k hk hbuf x hx
    simp at hx
    subst hx
    exact ⟨k, Nat.le_refl k, hk, hbuf, fun _ _ _ => rfl⟩
  | schritt s s' sN t hstep hrest iht =>
    intro hstoer k hk hbuf x hx
    have hstoer' : ∀ y ∈ t, FremdFrei y c a := by
      intro y hy
      exact hstoer y (by simp only [List.mem_cons]; exact Or.inr hy)
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hxt
    · exact ⟨k, Nat.le_refl k, hk, hbuf, fun _ _ _ => rfl⟩
    · match hstep with
      | .eigen hfl =>
        have hk8 : k < 8 := by
          have h8 : k = 8 ∨ k < 8 := by omega
          rcases h8 with rfl | hk8
          · have hempty : s.puffer c = [] := by
              rw [hbuf]
              rfl
            rw [flush_leer s c hempty] at hfl
            cases hfl
          · exact hk8
        have hhead : s.puffer c =
            ⟨addrOff a k, wortByte v k⟩ :: (wortEintraege a v).drop (k + 1) := by
          rw [hbuf]
          exact wortEintraege_kopf a v k hk8
        have hbuf' : s'.puffer c = (wortEintraege a v).drop (k + 1) :=
          flush_entfernt_kopf s s' c hfl _ _ hhead
        have hframe : ∀ j : Nat, k + 1 ≤ j → j < 8 →
            s'.mem.bytes (addrOff a j) = s.mem.bytes (addrOff a j) := by
          intro j hj hj8
          have hne : addrOff a j ≠
              (⟨addrOff a k, wortByte v k⟩ : TSOEintrag).addr :=
            addrOff_ne8 hj8 hk8 (by omega)
          exact flush_rahmen s s' c hfl _ _ hhead _ hne
        obtain ⟨k', hkk', hk'8, hbufN, hrestM⟩ :=
          iht hstoer' (k + 1) (by omega) hbuf' x hxt
        refine ⟨k', by omega, hk'8, hbufN, ?_⟩
        intro j hj hj8
        rw [hrestM j hj hj8]
        exact hframe j (by omega) hj8
      | .fremdSpülen d hne hfl =>
        have hown : s'.puffer c = s.puffer c :=
          flush_anderer_kern s s' d hfl (Ne.symm hne)
        have hbuf' : s'.puffer c = (wortEintraege a v).drop k := by
          rw [hown, hbuf]
        match hpd : s.puffer d with
        | [] =>
          have hnone : flushKern s d = none := flush_leer s d hpd
          rw [hnone] at hfl
          cases hfl
        | e :: rest =>
          have hmem_e : e ∈ s.puffer d := hpd ▸ by simp
          have hff : FremdFrei s c a := hstoer s (by simp)
          have hout : e.addr ∉ Fuss a := hff d hne e hmem_e
          have hframe : ∀ j : Nat, k ≤ j → j < 8 →
              s'.mem.bytes (addrOff a j) = s.mem.bytes (addrOff a j) := by
            intro j _ hj8
            have hmem_foot : addrOff a j ∈ Fuss a :=
              fuss_mem_offset a j hj8
            have hne_j : addrOff a j ≠ e.addr := by
              intro heq
              exact hout (heq ▸ hmem_foot)
            exact flush_rahmen s s' d hfl e rest hpd _ hne_j
          obtain ⟨k', hkk', hk'8, hbufN, hrestM⟩ :=
            iht hstoer' k hk hbuf' x hxt
          refine ⟨k', hkk', hk'8, hbufN, ?_⟩
          intro j hj hj8
          rw [hrestM j hj hj8]
          exact hframe j (by omega) hj8
      | .fremdAusgabe d e hne hissue =>
        have hown : s'.puffer c = s.puffer c :=
          issue_anderer_kern s s' d e.addr e.wert hissue (Ne.symm hne)
        have hbuf' : s'.puffer c = (wortEintraege a v).drop k := by
          rw [hown, hbuf]
        have hframe : ∀ j : Nat, k ≤ j → j < 8 →
            s'.mem.bytes (addrOff a j) = s.mem.bytes (addrOff a j) := by
          intro j _ _
          exact issue_kein_speicher s s' d e.addr e.wert hissue _
        obtain ⟨k', hkk', hk'8, hbufN, hrestM⟩ :=
          iht hstoer' k hk hbuf' x hxt
        refine ⟨k', hkk', hk'8, hbufN, ?_⟩
        intro j hj hj8
        rw [hrestM j hj hj8]
        exact hframe j (by omega) hj8

/-- FULL INTERMEDIATE PREFIX (generic): every visited state is
    exactly a stated prefix -- buffer suffix, installed bytes from
    the word, not-yet-drained bytes still from the start memory.
    Both halves feed the conclusion; the group pins the start. -/
theorem drainZwischen_voll (c : Nat) (a : Adresse) (v : Wort)
    (s sN : TSOZustand) (t : List TSOZustand)
    (hgrp : WortGruppe s c a v)
    (hspur : DrainSpur c s sN t)
    (hstoer : ∀ x ∈ t, FremdFrei x c a)
    (x : TSOZustand) (hx : x ∈ t) :
    ∃ k' : Nat, k' ≤ 8 ∧
      x.puffer c = (wortEintraege a v).drop k' ∧
      (∀ j : Nat, j < k' → x.mem.bytes (addrOff a j) = wortByte v j) ∧
      (∀ j : Nat, k' ≤ j → j < 8 →
        x.mem.bytes (addrOff a j) = s.mem.bytes (addrOff a j)) := by
  have hgrp1 := hgrp
  obtain ⟨hbufl, _hff⟩ := hgrp
  have hbase : s.puffer c = (wortEintraege a v).drop 0 := by
    rw [hbufl]
    rfl
  obtain ⟨k1, hk18, hbuf1, hinst⟩ :=
    drainZwischen_praefix c a v s sN t hgrp1 hspur hstoer x hx
  obtain ⟨k2, _hk0, hk28, hbuf2, hrest⟩ :=
    drainUninstalliert_bleibt_aux c a v s sN t hspur hstoer 0
      (Nat.zero_le 8) hbase x hx
  have hkk : k1 = k2 := by
    rw [hbuf1] at hbuf2
    have hlen := congrArg (fun l => (l.length)) hbuf2
    rw [List.length_drop, List.length_drop, wortEintraege_laenge] at hlen
    omega
  subst hkk
  exact ⟨k1, hk18, hbuf1, hinst, hrest⟩

/-! ## 4. Generic drain-equals-`write64` induction. -/

/-- DRAIN EQUALS WRITE-BYTES ON THE FOOTPRINT (generic): an
    exclusion-checked eight-drain installs exactly the `write64`
    footprint bytes. The group pins the start, the trace the prefix,
    end membership the witness state, emptiness the full eight, the
    exclusion every foreign step. -/
theorem drainFuss_gleich_schreibbytes (s sN : TSOZustand)
    (t : List TSOZustand) (c : Nat) (a : Adresse) (v : Wort)
    (hgrp : WortGruppe s c a v)
    (hspur : DrainSpur c s sN t) (hend : sN ∈ t)
    (hleer : sN.puffer c = [])
    (hstoer : ∀ x ∈ t, FremdFrei x c a) :
    ∀ j : Nat, j < 8 →
      sN.mem.bytes (addrOff a j) = writeBytes s.mem a v (addrOff a j) := by
  obtain ⟨k', hk'8, hbufN, hinst, _hrest⟩ :=
    drainZwischen_voll c a v s sN t hgrp hspur hstoer sN hend
  have hempty : (wortEintraege a v).drop k' = [] := by
    rw [← hbufN, hleer]
  have hlen0 := congrArg List.length hempty
  simp only [List.length_drop, wortEintraege_laenge,
    List.length_nil] at hlen0
  have hk_eq : k' = 8 := by omega
  subst hk_eq
  intro j hj
  rw [hinst j hj]
  have hhit := writeBytesN_hit s.mem a v 8 j hj (Nat.le_refl 8)
  show wortByte v j = writeBytes s.mem a v (addrOff a j)
  unfold writeBytes
  rw [hhit]

/-- DRAIN EQUALS `write64` (generic): an exclusion-checked eight-drain
    agrees with the successful `write64` on the whole footprint and
    reads back the word. The store equation feeds the footprint
    agreement, readability the accepted read-back, every other premise
    the footprint induction. -/
theorem drainGleichWrite64 (s sN : TSOZustand)
    (t : List TSOZustand) (c : Nat) (a : Adresse) (v : Wort)
    (m' : Speicher)
    (hgrp : WortGruppe s c a v) (hles : lesbar8 s.mem a = true)
    (hspur : DrainSpur c s sN t) (hend : sN ∈ t)
    (hleer : sN.puffer c = [])
    (hstoer : ∀ x ∈ t, FremdFrei x c a)
    (hwr : write64 s.mem a v = some m') :
    (∀ j : Nat, j < 8 →
      sN.mem.bytes (addrOff a j) = m'.bytes (addrOff a j)) ∧
      read64 sN.mem a = some v := by
  have hfoot := drainFuss_gleich_schreibbytes s sN t c a v
    hgrp hspur hend hleer hstoer
  have hread := wort_gruppe_liest_zurueck s sN t c a v
    hgrp hles hspur hend hleer hstoer
  have hmeq : ∀ x : Adresse,
      m'.bytes x = writeBytes s.mem a v x := by
    unfold write64 at hwr
    by_cases hc : schreibbar8 s.mem a = true
    · rw [if_pos hc] at hwr
      cases hwr
      intro x
      rfl
    · rw [if_neg hc] at hwr
      cases hwr
  refine ⟨?_, hread⟩
  intro j hj
  rw [hfoot j hj, hmeq]

/-! ## 5. Negative: a foreign overlapping flush breaks it.

  After a complete eight-drain (`grpS10`, accepted 603 state) a foreign
  entry inside the footprint flushes afterwards: byte three becomes 7
  while `write64` holds 5, so memory is observably not the written
  word. The exclusion premise is exactly what fails. -/

/-- Overlapping foreign byte: 7 (word byte three of `zeugenWort` is 5). -/
def ovFremd : Byte := BitVec.ofNat 8 7

/-- Overlap state: drained memory with a foreign footprint entry. -/
def ovS0 : TSOZustand :=
  ⟨grpS10.mem, pufferSetze grpS10.puffer 1
    [⟨addrOff (0 : Adresse) 3, ovFremd⟩]⟩

/-- After the foreign flush: byte three carries the foreign byte. -/
def ovS1 : TSOZustand :=
  ⟨{ ovS0.mem with bytes := fun x =>
      if x = addrOff (0 : Adresse) 3 then ovFremd
      else ovS0.mem.bytes x },
    pufferSetze ovS0.puffer 1 []⟩

/-- The foreign flush computes as claimed. -/
theorem ov_flush : flushKern ovS0 1 = some ovS1 := by rfl

/-- The overlapping entry breaks foreign-footprint freedom. -/
theorem ov_kein_fremdfrei : ¬ FremdFrei ovS0 0 (0 : Adresse) := by
  intro h
  have hmem : (⟨addrOff (0 : Adresse) 3, ovFremd⟩ : TSOEintrag) ∈
      ovS0.puffer 1 := by
    have heq : ovS0.puffer 1 =
        [⟨addrOff (0 : Adresse) 3, ovFremd⟩] := by
      simp [ovS0, pufferSetze]
    rw [heq]
    simp
  exact (h 1 (by decide) _ hmem)
    (fuss_mem_offset (0 : Adresse) 3 (by decide))

/-- The foreign flush breaks the footprint: byte three is 7, not 5. -/
theorem ov_byte_bricht :
    ovS1.mem.bytes (addrOff (0 : Adresse) 3) ≠
      writeBytes grpS2.mem (0 : Adresse) zeugenWort
        (addrOff (0 : Adresse) 3) := by
  decide

/-- The foreign flush breaks the read-back: the word no longer reads. -/
theorem ov_read_bricht :
    read64 ovS1.mem (0 : Adresse) ≠ some zeugenWort := by
  intro heq
  have hles : lesbar8 ovS1.mem (0 : Adresse) = true := by rfl
  unfold read64 at heq
  rw [if_pos hles] at heq
  simp only [Option.some.injEq] at heq
  have heqb := congrArg (fun w => wortByte w 3) heq
  rw [fwd_wortByte_bytesWort3] at heqb
  have hbyte : ovS1.mem.bytes (addrOff (0 : Adresse) 3) =
      wortByte zeugenWort 3 := heqb
  have hne : ovS1.mem.bytes (addrOff (0 : Adresse) 3) ≠
      wortByte zeugenWort 3 := by decide
  exact hne hbyte

/-! ## 6. Joint witness: two cores, store, forward, drain.

  Core 0 buffers word 42 at address 8184 through the family adapter;
  core 0 forwards it while core 1 still reads zero; after core 0
  drains, shared memory holds the `write64` footprint for both cores.
  The drain observably changes memory (0 becomes 42). Beside it stand
  the planted guard, dark-read and empty-drain refusals. -/

/-- Witness bytes: zeroed everywhere. -/
def drainWitBytes (_ : Adresse) : Byte := BitVec.ofNat 8 0

/-- Witness data permission: sixteen bytes at 8176. -/
def drainWitDaten (a : Adresse) : Bool :=
  decide (8176 ≤ a.toNat ∧ a.toNat < 8192)

/-- Witness code permission: fifteen bytes at 4096. -/
def drainWitCode (a : Adresse) : Bool :=
  decide (4096 ≤ a.toNat ∧ a.toNat < 4111)

/-- Witness shared memory: zeroed bytes, data RW, code X-only. -/
def drainWitMem : Speicher :=
  { bytes := drainWitBytes, lesbar := drainWitDaten,
    schreibbar := drainWitDaten, ausfuehrbar := drainWitCode }

/-- Witness core-0 registers: top at 8192, `rax` holding 9. -/
def drainWitReg0 : Register → Wort := fun q =>
  if q = Register.rsp then BitVec.ofNat 64 8192
  else if q = Register.rax then BitVec.ofNat 64 9
  else BitVec.ofNat 64 0

/-- Witness core-1 registers: top at 8184. -/
def drainWitReg1 : Register → Wort := fun q =>
  if q = Register.rsp then BitVec.ofNat 64 8184
  else BitVec.ofNat 64 0

/-- Witness core data: core 0 runs at 4096, core 1 idles at 8192. -/
def drainWitKern : Nat → HwKern
  | 0 => ⟨drainWitReg0, zeugeFlags, BitVec.ofNat 64 4096,
      (fun _ => BitVec.ofNat 128 0), kontextReset⟩
  | _ => ⟨drainWitReg1, zeugeFlags, BitVec.ofNat 64 8192,
      (fun _ => BitVec.ofNat 128 0), kontextReset⟩

/-- Witness start machine: shared memory, two cores, empty buffers,
    full silicon with OS vector state. -/
def drainWitM0 : HwMaschine :=
  ⟨drainWitMem, drainWitKern, fun _ => [], basisHw, fun _ => basisBereit⟩

/-- Witness word address. -/
def drainWitAdr : Adresse := BitVec.ofNat 64 8184

/-- Witness stored word. -/
def drainWitWort : Wort := BitVec.ofNat 64 42

/-- Witness zero word. -/
def drainWitNull : Wort := BitVec.ofNat 64 0

/-- Witness pushed machine: core 0 carries the exact eight entries,
    core 1 is empty. The adapter reaches exactly this state. -/
def drainWitM1 : HwMaschine :=
  setTso drainWitM0 ⟨drainWitMem, fun d =>
    if d = 0 then wortEintraege drainWitAdr drainWitWort else []⟩

/-- Core 0 stores word 42 at the witness address through the
    family adapter. -/
def drainWitPush : Option HwMaschine :=
  drainAdapter.schritt drainWitM0 0 (.speichere drainWitAdr drainWitWort)

/-- Buffered entry count on core 0 after the store. -/
def drainWitBufLen : Option Nat :=
  match drainWitPush with
  | some m1 => some (m1.puffer 0).length
  | none => none

/-- Shared-memory byte at the address right after the store. -/
def drainWitMemStill : Option Byte :=
  match drainWitPush with
  | some m1 => some (m1.mem.bytes drainWitAdr)
  | none => none

/-- Core 0 observes its own buffered word (forwarding). -/
def drainWitLoadEigen : Option (Option Wort) :=
  match drainWitPush with
  | some m1 => some (stapelLadeWort (tsoAnsicht m1) 0 drainWitAdr)
  | none => none

/-- Core 1 observes the old word (no foreign forwarding). -/
def drainWitLoadFremd : Option (Option Wort) :=
  match drainWitPush with
  | some m1 => some (stapelLadeWort (tsoAnsicht m1) 1 drainWitAdr)
  | none => none

/-- First own-drain step through the family adapter. -/
def drainWitEigen : Option HwMaschine :=
  match drainWitPush with
  | some m1 => drainAdapter.schritt m1 0 .eigenSpuele
  | none => none

/-- Buffered entry count on core 0 after the first drain step. -/
def drainWitEigenLen : Option Nat :=
  match drainWitEigen with
  | some m => some (m.puffer 0).length
  | none => none

/-- Core 0 drains its oldest entry, eight times chained. -/
def drainWitD1 : Option TSOZustand :=
  match drainWitPush with
  | some m1 => flushKern (tsoAnsicht m1) 0
  | none => none

def drainWitD2 : Option TSOZustand :=
  match drainWitD1 with
  | some s => flushKern s 0
  | none => none

def drainWitD3 : Option TSOZustand :=
  match drainWitD2 with
  | some s => flushKern s 0
  | none => none

def drainWitD4 : Option TSOZustand :=
  match drainWitD3 with
  | some s => flushKern s 0
  | none => none

def drainWitD5 : Option TSOZustand :=
  match drainWitD4 with
  | some s => flushKern s 0
  | none => none

def drainWitD6 : Option TSOZustand :=
  match drainWitD5 with
  | some s => flushKern s 0
  | none => none

def drainWitD7 : Option TSOZustand :=
  match drainWitD6 with
  | some s => flushKern s 0
  | none => none

def drainWitD8 : Option TSOZustand :=
  match drainWitD7 with
  | some s => flushKern s 0
  | none => none

/-- Shared memory after the full drain. -/
def drainWitNachFlush : Option Speicher :=
  match drainWitD8 with
  | some s => some s.mem
  | none => none

/-- The word read from shared memory after the drain. -/
def drainWitNachRead : Option (Option Wort) :=
  match drainWitNachFlush with
  | some mem => some (read64 mem drainWitAdr)
  | none => none

/-- Core 1 reads the drained word from shared memory. -/
def drainWitFremdNachFlush : Option (Option Wort) :=
  match drainWitD8 with
  | some s => some (stapelLadeWort s 1 drainWitAdr)
  | none => none

/-! ## 7. Witness facts: the reached run forwards, then drains. -/

/-- The witness machine is well-formed: full silicon admits all. -/
theorem drainWit_wf : HwWf drainWitM0 := by
  intro c f _
  cases f <;> rfl

/-- The store buffers exactly eight entries on core 0. -/
theorem drainWit_puffer8 : drainWitBufLen = some 8 := by
  decide

/-- The store leaves the shared address byte at zero. -/
theorem drainWit_mem_still :
    drainWitMemStill = some (BitVec.ofNat 8 0) := by
  decide

/-- Forwarding on the reached run: core 0 reads its own word 42. -/
theorem drainWit_weiterleitung :
    drainWitLoadEigen = some (some drainWitWort) := by
  decide

/-- No foreign forwarding on the reached run: core 1 reads zero. -/
theorem drainWit_fremd_alt :
    drainWitLoadFremd = some (some drainWitNull) := by
  decide

/-- The first adapter drain step leaves seven entries. -/
theorem drainWit_eigen_sieben : drainWitEigenLen = some 7 := by
  decide

/-- The drain changes shared memory: the address reads 42. -/
theorem drainWit_spuelung_aendert_speicher :
    drainWitNachRead = some (some drainWitWort) := by
  decide

/-- After the drain core 1 observes the new word. -/
theorem drainWit_fremd_neu :
    drainWitFremdNachFlush = some (some drainWitWort) := by
  decide

/-- The address starts zeroed: the run really changes memory. -/
theorem drainWit_anfang_null :
    drainWitMem.bytes drainWitAdr = BitVec.ofNat 8 0 := by
  decide

/-- The pushed buffer carries exactly the word entries. -/
theorem drainWit_pufferform :
    (tsoAnsicht drainWitM1).puffer 0 =
      wortEintraege drainWitAdr drainWitWort := by
  decide

/-- No foreign entry touches the footprint on the witness. -/
theorem drainWit_fremdfrei :
    FremdFrei (tsoAnsicht drainWitM1) 0 drainWitAdr := by
  intro d hd e hm
  have hbuf : (tsoAnsicht drainWitM1).puffer d = [] := by
    simp only [tsoAnsicht, drainWitM1, setTso]
    rw [if_neg hd]
  rw [hbuf] at hm
  cases hm

/-- The pushed state satisfies the group guard. -/
theorem drainWit_gruppe :
    WortGruppe (tsoAnsicht drainWitM1) 0 drainWitAdr drainWitWort :=
  ⟨drainWit_pufferform, drainWit_fremdfrei⟩

/-- Every footprint byte is readable on the witness. -/
theorem drainWit_lesbar_all (k : Nat) (hk : k < 8) :
    (tsoAnsicht drainWitM1).mem.lesbar (addrOff drainWitAdr k) = true := by
  have haddr : (addrOff drainWitAdr k).toNat = 8184 + k := by
    unfold addrOff drainWitAdr
    rw [BitVec.toNat_add]
    have e1 : (BitVec.ofNat 64 8184).toNat = 8184 := by
      rw [BitVec.toNat_ofNat]
    have e2 : (BitVec.ofNat 64 k).toNat = k := by
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by omega)
    rw [e1, e2]
    exact Nat.mod_eq_of_lt (by omega)
  show drainWitDaten (addrOff drainWitAdr k) = true
  unfold drainWitDaten
  rw [decide_eq_true_eq]
  omega

/-! ## 8. Generic fires on the accepted eight-drain.

  The accepted 603 witness (`grpS2` to `grpS10`) satisfies every
  premise jointly, so the generic induction fires on it: footprint
  bytes equal the `write64` bytes, the option equation agrees, and a
  mid-trace state is exactly its prefix. -/

/-- The `write64` of the grouped word succeeds on the witness start. -/
theorem drainGrp_hwr :
    write64 grpS2.mem (0 : Adresse) zeugenWort = some zeugenSpeicherNach := by
  show write64 zeugenSpeicher (0 : Adresse) zeugenWort =
    some zeugenSpeicherNach
  unfold write64
  have hc : schreibbar8 zeugenSpeicher (0 : Adresse) = true := rfl
  rw [if_pos hc]
  rfl

/-- GENERIC FOOTPRINT FIRE: the drained bytes are the `write64` bytes. -/
theorem drainGrp_fuss (j : Nat) (hj : j < 8) :
    grpS10.mem.bytes (addrOff (0 : Adresse) j) =
      writeBytes grpS2.mem (0 : Adresse) zeugenWort
        (addrOff (0 : Adresse) j) :=
  drainFuss_gleich_schreibbytes grpS2 grpS10 _ 0 (0 : Adresse) zeugenWort
    grp_hgrp grp_spur grp_hend grp_hempty grp_hstoer j hj

/-- GENERIC `write64` FIRE: footprint agreement plus read-back. -/
theorem drainGrp_write64 :
    (∀ j : Nat, j < 8 →
      grpS10.mem.bytes (addrOff (0 : Adresse) j) =
        zeugenSpeicherNach.bytes (addrOff (0 : Adresse) j)) ∧
      read64 grpS10.mem (0 : Adresse) = some zeugenWort :=
  drainGleichWrite64 grpS2 grpS10 _ 0 (0 : Adresse) zeugenWort
    zeugenSpeicherNach grp_hgrp grp_hles grp_spur grp_hend grp_hempty
    grp_hstoer drainGrp_hwr

/-- GENERIC MID-TRACE FIRE: the fourth visited state is exactly its
    prefix (three installed, five still from the start). -/
theorem drainGrp_mitte :
    ∃ k' : Nat, k' ≤ 8 ∧
      grpS5.puffer 0 = (wortEintraege (0 : Adresse) zeugenWort).drop k' ∧
      (∀ j : Nat, j < k' →
        grpS5.mem.bytes (addrOff (0 : Adresse) j) = wortByte zeugenWort j) ∧
      (∀ j : Nat, k' ≤ j → j < 8 →
        grpS5.mem.bytes (addrOff (0 : Adresse) j) =
          grpS2.mem.bytes (addrOff (0 : Adresse) j)) :=
  drainZwischen_voll 0 (0 : Adresse) zeugenWort grpS2 grpS10 _ grp_hgrp
    grp_spur grp_hstoer grpS5 (by simp)

/-! ## 9. Refusal witnesses. -/

/-- Guard witness memory: nothing is writable. -/
def drainWitGuardMem : Speicher :=
  { bytes := drainWitBytes, lesbar := drainWitDaten,
    schreibbar := fun _ => false, ausfuehrbar := drainWitCode }

/-- Guard witness machine: same cores, write-protected memory. -/
def drainWitGuardM0 : HwMaschine :=
  ⟨drainWitGuardMem, drainWitKern, fun _ => [], basisHw,
    fun _ => basisBereit⟩

/-- Dark witness memory: nothing is readable. -/
def drainWitDarkMem : Speicher :=
  { bytes := drainWitBytes, lesbar := fun _ => false,
    schreibbar := drainWitDaten, ausfuehrbar := drainWitCode }

/-- The guard denies the first footprint byte. -/
theorem drainWit_guard_dicht :
    drainWitGuardM0.mem.schreibbar (addrOff drainWitAdr 0) = false := by
  decide

/-- Guard store refuses on the witness, through the generic refusal. -/
theorem drainWit_guard_speichere_verweigert :
    drainAdapter.schritt drainWitGuardM0 0
      (.speichere drainWitAdr drainWitWort) = none :=
  drainSpeichere_wache _ _ _ _ drainWit_guard_dicht

/-- The dark page denies the first footprint byte. -/
theorem drainWit_dark_dicht :
    drainWitDarkMem.lesbar (addrOff drainWitAdr 0) = false := by
  decide

/-- Dark observation refuses on the witness. -/
theorem drainWit_dark_beob_verweigert :
    stapelLadeWort ⟨drainWitDarkMem, fun _ => []⟩ 0 drainWitAdr = none :=
  drainBeobachte_dunkel _ _ _ drainWit_dark_dicht

/-- Empty own drain refuses on the witness start machine. -/
theorem drainWit_eigen_leer_verweigert :
    drainAdapter.schritt drainWitM0 0 .eigenSpuele = none :=
  drainEigen_leer_verweigert _ _ rfl

/-! ## 10. Joint witness.

  Every duty premise holds jointly on reached, non-degenerate runs:
  the group guard with readability, owner-only forwarding of 42 on two
  cores, an adapter drain step, a full drain changing shared memory 0
  to 42 observed from both cores, the generic footprint/`write64`
  fires with a mid-trace prefix -- beside the planted guard,
  dark-read and empty-drain refusals and the overlapping-flush break
  (exclusion failure, wrong byte, wrong read-back). -/

/-- JOINT WITNESS. -/
theorem drainGeneric_zeuge :
    HwWf drainWitM0 ∧
      WortGruppe (tsoAnsicht drainWitM1) 0 drainWitAdr drainWitWort ∧
      (∀ k, k < 8 →
        (tsoAnsicht drainWitM1).mem.lesbar (addrOff drainWitAdr k) =
          true) ∧
      (1 : Nat) ≠ 0 ∧
      drainWitBufLen = some 8 ∧
      drainWitMemStill = some (BitVec.ofNat 8 0) ∧
      drainWitLoadEigen = some (some drainWitWort) ∧
      drainWitLoadFremd = some (some drainWitNull) ∧
      drainWitEigenLen = some 7 ∧
      drainWitNachRead = some (some drainWitWort) ∧
      drainWitFremdNachFlush = some (some drainWitWort) ∧
      drainWitMem.bytes drainWitAdr = BitVec.ofNat 8 0 ∧
      (∀ j, j < 8 →
        grpS10.mem.bytes (addrOff (0 : Adresse) j) =
          writeBytes grpS2.mem (0 : Adresse) zeugenWort
            (addrOff (0 : Adresse) j)) ∧
      ((∀ j : Nat, j < 8 →
        grpS10.mem.bytes (addrOff (0 : Adresse) j) =
          zeugenSpeicherNach.bytes (addrOff (0 : Adresse) j)) ∧
        read64 grpS10.mem (0 : Adresse) = some zeugenWort) ∧
      (∃ k' : Nat, k' ≤ 8 ∧
        grpS5.puffer 0 = (wortEintraege (0 : Adresse) zeugenWort).drop k' ∧
        (∀ j : Nat, j < k' →
          grpS5.mem.bytes (addrOff (0 : Adresse) j) = wortByte zeugenWort j) ∧
        (∀ j : Nat, k' ≤ j → j < 8 →
          grpS5.mem.bytes (addrOff (0 : Adresse) j) =
            grpS2.mem.bytes (addrOff (0 : Adresse) j))) ∧
      drainWitGuardM0.mem.schreibbar (addrOff drainWitAdr 0) = false ∧
      drainAdapter.schritt drainWitGuardM0 0
        (.speichere drainWitAdr drainWitWort) = none ∧
      drainWitDarkMem.lesbar (addrOff drainWitAdr 0) = false ∧
      stapelLadeWort ⟨drainWitDarkMem, fun _ => []⟩ 0 drainWitAdr =
        none ∧
      drainAdapter.schritt drainWitM0 0 .eigenSpuele = none ∧
      ¬ FremdFrei ovS0 0 (0 : Adresse) ∧
      flushKern ovS0 1 = some ovS1 ∧
      ovS1.mem.bytes (addrOff (0 : Adresse) 3) ≠
        writeBytes grpS2.mem (0 : Adresse) zeugenWort
          (addrOff (0 : Adresse) 3) ∧
      read64 ovS1.mem (0 : Adresse) ≠ some zeugenWort := by
  exact ⟨drainWit_wf, drainWit_gruppe, drainWit_lesbar_all, by decide,
    drainWit_puffer8, drainWit_mem_still, drainWit_weiterleitung,
    drainWit_fremd_alt, drainWit_eigen_sieben,
    drainWit_spuelung_aendert_speicher, drainWit_fremd_neu,
    drainWit_anfang_null, drainGrp_fuss, drainGrp_write64, drainGrp_mitte,
    drainWit_guard_dicht, drainWit_guard_speichere_verweigert,
    drainWit_dark_dicht, drainWit_dark_beob_verweigert,
    drainWit_eigen_leer_verweigert, ov_kein_fremdfrei, ov_flush,
    ov_byte_bricht, ov_read_bricht⟩

/- CUTS:
   Proved here (all over the REUSED canonical `Zustand`/`Speicher`
   vocabulary, the accepted `HwMaschine`/`HwSchritt`/`HwWf`,
   `issueByte`/`loadByte`/`flushKern`, `wortEintraege`,
   `WortGruppe`/`FremdFrei`/`DrainSpur`, `hwWortAusgabe`,
   `stapelLadeWort`, `read64`/`write64`/`writeBytes` -- no new
   machine, no new decoder row, no new instruction, no source claim):
   - family events `DrainEreignis` and the adapter `drainAdapter`
     (stores buffer a word, own/foreign drains flush, foreign issues
     buffer, observations read without moving state); every adapter
     step preserves `HwWf` (`drainAdapter_wf`);
   - buffer agreement: stores append exactly the canonical eight
     entries (`drainSpeichere_puffer`) and change no shared-memory
     byte (`drainSpeichere_kein_speicher`); observations move no
     state (`drainBeobachte_still`); own drains are the accepted
     flush (`drainEigen_ist_flush`) and a machine flush event
     (`drainEigen_ist_schritt`);
   - GENERIC PREFIXES: every visited drain state is exactly a stated
     prefix -- buffer suffix with installed bytes
     (`drainZwischen_praefix` over `drain_installiert_aux`),
     not-yet-drained bytes still from the start memory
     (`drainUninstalliert_bleibt_aux`, new induction over
     `DrainSpur`), joined (`drainZwischen_voll`);
   - DRAIN EQUALS `write64` (generic): exclusion-checked eight-drains
     install exactly the `write64` footprint bytes
     (`drainFuss_gleich_schreibbytes`) and agree with the successful
     `write64` with read-back (`drainGleichWrite64` over the accepted
     `wort_gruppe_liest_zurueck`);
   - negative: a foreign overlapping flush breaks the footprint, the
     read-back and the exclusion (`ov_flush`, `ov_kein_fremdfrei`,
     `ov_byte_bricht`, `ov_read_bricht` over the accepted 603 drain
     end `grpS10`; word byte three of `zeugenWort` is 5, the foreign
     byte is 7);
   - planted refusals: guard stores (`drainSpeichere_wache` via
     `issueListe_cons_none`), dark observations
     (`drainBeobachte_dunkel` via `stapelPop_unlesbar`), empty own
     drains (`drainEigen_leer_verweigert` via `flush_leer`);
   - joint non-degenerate two-core witness (`drainGeneric_zeuge`):
     adapter store of 42 with owner-only forwarding, an adapter
     drain step (8 to 7), a full drain changing shared memory 0 to
     42 observed from both cores, the generic fires on the accepted
     eight-drain with a mid-trace prefix, beside guard, dark-read
     and empty-drain refusals and the overlapping-flush break.
   NOT proved here, and not claimed:
   - No silicon correspondence: encodings are the accepted
     canonical subsets with self-consistency only, not x86 truth.
     Alignment carries no gate in this model (the byte drain is
     alignment-agnostic by `WortGruppe` design). The Intel SDM
     extracts supplied to the clone were consulted for ordering
     (TSO store-issue FIFO, youngest-own forwarding, no multi-byte
     atomicity); they are provenance, not proofs.
   - No global memory equality with `write64`: foreign flushes
     satisfying `FremdFrei` are real steps that change disjoint
     bytes, so equality holds on the grouped footprint (and, via
     the accepted `wort_gruppe_rahmen`, on separately guarded
     footprints), never whole-memory.
   - No LOCK/RMW, fault, interrupt, addressed/SIB, FP-control or
     SIMD path; no source/IR/ABI/loader/entry/budget link; no
     target-to-W/GX simulation; no whole-word atomicity beyond
     `WortGruppe`-guarded byte drains.
   - `drainZwischen_praefix` and the 603 `verflochten_*` wrappers
     overlap in scope (all over `drain_installiert_aux`); this lane
     adds the uninstall-preserved half, the `write64` footprint
     equation and the machine adapter, and cites -- never
     duplicates -- the accepted statements.
-/

#print axioms DrainEreignis
#print axioms drainAdapter
#print axioms drainAdapter_wf
#print axioms drainSpeichere_puffer
#print axioms drainSpeichere_kein_speicher
#print axioms drainEigen_ist_flush
#print axioms drainEigen_ist_schritt
#print axioms drainBeobachte_still
#print axioms drainEigen_leer_verweigert
#print axioms drainSpeichere_wache
#print axioms drainBeobachte_dunkel
#print axioms drainZwischen_praefix
#print axioms drainUninstalliert_bleibt_aux
#print axioms drainZwischen_voll
#print axioms drainFuss_gleich_schreibbytes
#print axioms drainGleichWrite64
#print axioms ov_flush
#print axioms ov_kein_fremdfrei
#print axioms ov_byte_bricht
#print axioms ov_read_bricht
#print axioms drainWit_wf
#print axioms drainWit_gruppe
#print axioms drainWit_lesbar_all
#print axioms drainWit_weiterleitung
#print axioms drainGrp_hwr
#print axioms drainGrp_fuss
#print axioms drainGrp_write64
#print axioms drainGrp_mitte
#print axioms drainWit_guard_speichere_verweigert
#print axioms drainWit_dark_beob_verweigert
#print axioms drainWit_eigen_leer_verweigert
#print axioms drainGeneric_zeuge

end Gabbro.Grammatik.X86
