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

/- CUTS:
   Skeleton only: adapter defined, induction and witnesses open.
-/

#print axioms drainAdapter

end Gabbro.Grammatik.X86
