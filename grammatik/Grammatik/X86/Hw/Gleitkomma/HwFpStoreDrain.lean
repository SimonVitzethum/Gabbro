/-
  File:      Grammatik/X86/HwFpStoreDrain.lean
  Subject:   FP 32-bit store drain equals the accepted `write32`.

  Lane 1307 (follow-up of lane 1211 `HwFpDispatch.lean`): the
  drain/write32 byte correspondence for STMXCSR and MOVSS-store was
  open (value and footprint pinned at issue level only). This file
  proves, generically over the TSO model and the `FpFremdFrei32`
  guard, that the four buffered byte entries drain to canonical
  memory equal to the accepted `write32` of the stored value (the
  `HwDrainGeneric.lean` technique for 8 bytes, specialised to 4),
  with forwarding to the owner and the foreign view before drain; a
  misaligned 4-byte store crossing a group boundary stays as the
  accepted tearing refusal. Accepted evaluators are lifted, never
  redefined.
-/
import Grammatik.X86.Hw.Grundlage.HardwareExecution
import Grammatik.X86.Hw.Gleitkomma.HwFpControl
import Grammatik.X86.Hw.Gleitkomma.HwFpDispatch
import Grammatik.X86.Hw.Speicher.HwDrainGeneric
import Grammatik.X86.TSO.Kern.WordAccessGrouping

namespace Gabbro.Grammatik.X86

/-- FP 32-bit store-drain family events on the coherent machine. -/
inductive FpStoreEreignis where
  | speichere32 : Adresse → Wort → FpStoreEreignis
  | eigenSpuele : FpStoreEreignis
  | fremdSpuele : Nat → FpStoreEreignis
  | fremdAusgabe : Nat → TSOEintrag → FpStoreEreignis
  | beobachte : Adresse → FpStoreEreignis
  deriving DecidableEq, Repr

/-- The family adapter: 32-bit stores buffer four bytes, drains
    flush, observations read without moving state. -/
def fpStoreAdapter : HwAdapter FpStoreEreignis :=
  ⟨fun m c ev => match ev with
    | .speichere32 a v => fpCtrlAusgabe32 m c a v
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
      match loadByte (tsoAnsicht m) c a with
      | some _ => some m
      | none => none⟩

/-! ## 2. Adapter duties: well-formedness, agreement, embedding. -/

/-- Every adapter step preserves well-formedness: stores, flushes and
    issues ride `setTso`, observations are silent. -/
theorem fpStoreAdapter_wf (m : HwMaschine) (c : Nat)
    (ev : FpStoreEreignis) (m' : HwMaschine)
    (h : fpStoreAdapter.schritt m c ev = some m') (hwf : HwWf m) :
    HwWf m' := by
  cases ev with
  | speichere32 a v =>
    have had : fpStoreAdapter.schritt m c (.speichere32 a v) =
        fpCtrlAusgabe32 m c a v := rfl
    rw [had] at h
    unfold fpCtrlAusgabe32 at h
    cases h1 : issueListe (tsoAnsicht m) c (fpEintraege32 a v) with
    | none => rw [h1] at h; cases h
    | some s' => rw [h1] at h; cases h; exact setTso_wf _ s' hwf
  | eigenSpuele =>
    cases hfl : flushKern (tsoAnsicht m) c with
    | none =>
      have hh : fpStoreAdapter.schritt m c .eigenSpuele = none := by
        show (match flushKern (tsoAnsicht m) c with
          | some s' => some (setTso m s') | none => none) = none
        rw [hfl]
      rw [hh] at h; cases h
    | some s' =>
      have hh : fpStoreAdapter.schritt m c .eigenSpuele =
          some (setTso m s') := by
        show (match flushKern (tsoAnsicht m) c with
          | some s' => some (setTso m s') | none => none) = _
        rw [hfl]
      rw [hh] at h; cases h; exact setTso_wf _ s' hwf
  | fremdSpuele d =>
    cases hfl : flushKern (tsoAnsicht m) d with
    | none =>
      have hh : fpStoreAdapter.schritt m c (.fremdSpuele d) = none := by
        show (match flushKern (tsoAnsicht m) d with
          | some s' => some (setTso m s') | none => none) = none
        rw [hfl]
      rw [hh] at h; cases h
    | some s' =>
      have hh : fpStoreAdapter.schritt m c (.fremdSpuele d) =
          some (setTso m s') := by
        show (match flushKern (tsoAnsicht m) d with
          | some s' => some (setTso m s') | none => none) = _
        rw [hfl]
      rw [hh] at h; cases h; exact setTso_wf _ s' hwf
  | fremdAusgabe d e =>
    cases hfl : issueByte (tsoAnsicht m) d e.addr e.wert with
    | none =>
      have hh : fpStoreAdapter.schritt m c (.fremdAusgabe d e) = none := by
        show (match issueByte (tsoAnsicht m) d e.addr e.wert with
          | some s' => some (setTso m s') | none => none) = none
        rw [hfl]
      rw [hh] at h; cases h
    | some s' =>
      have hh : fpStoreAdapter.schritt m c (.fremdAusgabe d e) =
          some (setTso m s') := by
        show (match issueByte (tsoAnsicht m) d e.addr e.wert with
          | some s' => some (setTso m s') | none => none) = _
        rw [hfl]
      rw [hh] at h; cases h; exact setTso_wf _ s' hwf
  | beobachte a =>
    cases hl : loadByte (tsoAnsicht m) c a with
    | none =>
      have hh : fpStoreAdapter.schritt m c (.beobachte a) = none := by
        show (match loadByte (tsoAnsicht m) c a with
          | some _ => some m | none => none) = none
        rw [hl]
      rw [hh] at h; cases h
    | some w =>
      have hh : fpStoreAdapter.schritt m c (.beobachte a) = some m := by
        show (match loadByte (tsoAnsicht m) c a with
          | some _ => some m | none => none) = some m
        rw [hl]
      rw [hh] at h; cases h; exact hwf

/-- A buffered 32-bit store appends exactly the canonical four entries. -/
theorem fpStoreSpeichere_puffer (m : HwMaschine) (c : Nat)
    (a : Adresse) (v : Wort) (m' : HwMaschine)
    (h : fpStoreAdapter.schritt m c (.speichere32 a v) = some m') :
    m'.puffer c = m.puffer c ++ fpEintraege32 a v :=
  fpCtrlAusgabe32_puffer m c a v m' h

/-- A buffered 32-bit store changes no shared-memory byte. -/
theorem fpStoreSpeichere_kein_speicher (m : HwMaschine) (c : Nat)
    (a : Adresse) (v : Wort) (m' : HwMaschine)
    (h : fpStoreAdapter.schritt m c (.speichere32 a v) = some m')
    (x : Adresse) :
    m'.mem.bytes x = m.mem.bytes x :=
  fpCtrlAusgabe32_kein_speicher m c a v m' h x

/-- An own-drain adapter step IS the accepted oldest-entry flush. -/
theorem fpStoreEigen_ist_flush (m : HwMaschine) (c : Nat)
    (s' : TSOZustand)
    (hfl : flushKern (tsoAnsicht m) c = some s') (m' : HwMaschine)
    (h : fpStoreAdapter.schritt m c .eigenSpuele = some m') :
    m' = setTso m s' := by
  have hh : fpStoreAdapter.schritt m c .eigenSpuele =
      some (setTso m s') := by
    show (match flushKern (tsoAnsicht m) c with
      | some s' => some (setTso m s') | none => none) = _
    rw [hfl]
  rw [hh] at h
  exact (Option.some.inj h).symm

/-- An own-drain adapter step is a machine flush event. -/
theorem fpStoreEigen_ist_schritt (m : HwMaschine) (c : Nat)
    (s' : TSOZustand) (e : TSOEintrag)
    (hfl : flushKern (tsoAnsicht m) c = some s')
    (hkopf : (m.puffer c).head? = some e) :
    HwSchritt m (setTso m s') (.spülung c e) :=
  .spüle c e s' hfl hkopf

/-- A successful observation moves no state. -/
theorem fpStoreBeobachte_still (m : HwMaschine) (c : Nat) (a : Adresse)
    (v : Byte) (h : loadByte (tsoAnsicht m) c a = some v) :
    fpStoreAdapter.schritt m c (.beobachte a) = some m := by
  show (match loadByte (tsoAnsicht m) c a with
    | some _ => some m | none => none) = _
  rw [h]

/-- EMPTY DRAIN REFUSES: flushing an empty own buffer admits no step. -/
theorem fpStoreEigen_leer_verweigert (m : HwMaschine) (c : Nat)
    (hleer : m.puffer c = []) :
    fpStoreAdapter.schritt m c .eigenSpuele = none := by
  have hfl : flushKern (tsoAnsicht m) c = none := by
    apply flush_leer
    simpa [tsoAnsicht] using hleer
  show (match flushKern (tsoAnsicht m) c with
    | some s' => some (setTso m s') | none => none) = none
  rw [hfl]

/-- GUARD STORE REFUSES: without write permission at the first byte
    the whole 32-bit fold refuses. -/
theorem fpStoreSpeichere_wache (m : HwMaschine) (c : Nat)
    (a : Adresse) (v : Wort)
    (hguard : m.mem.schreibbar (addrOff a 0) = false) :
    fpStoreAdapter.schritt m c (.speichere32 a v) = none := by
  have had : fpStoreAdapter.schritt m c (.speichere32 a v) =
      fpCtrlAusgabe32 m c a v := rfl
  rw [had]
  unfold fpCtrlAusgabe32
  have hfirst : issueByte (tsoAnsicht m) c (addrOff a 0)
      (wortByte v 0) = none :=
    issue_verweigert _ _ _ _
      (by simpa [tsoAnsicht_speicher] using hguard)
  have hcons : fpEintraege32 a v =
      ⟨addrOff a 0, wortByte v 0⟩ ::
      [⟨addrOff a 1, wortByte v 1⟩,
       ⟨addrOff a 2, wortByte v 2⟩,
       ⟨addrOff a 3, wortByte v 3⟩] := rfl
  have hfold : issueListe (tsoAnsicht m) c
      (⟨addrOff a 0, wortByte v 0⟩ ::
      [⟨addrOff a 1, wortByte v 1⟩,
       ⟨addrOff a 2, wortByte v 2⟩,
       ⟨addrOff a 3, wortByte v 3⟩]) = none :=
    issueListe_cons_none _ _ _ _ hfirst
  rw [hcons, hfold]

/-- DARK OBSERVATION REFUSES: without read permission the byte
    observation refuses. -/
theorem fpStoreBeobachte_dunkel (m : HwMaschine) (c : Nat) (a : Adresse)
    (hguard : (tsoAnsicht m).mem.lesbar a = false) :
    fpStoreAdapter.schritt m c (.beobachte a) = none := by
  have hl : loadByte (tsoAnsicht m) c a = none :=
    load_verweigert _ _ _ hguard
  show (match loadByte (tsoAnsicht m) c a with
    | some _ => some m | none => none) = none
  rw [hl]

/-! ## 3. Four-byte drain induction: drain equals `write32`.

  The `HwDrainGeneric.lean` technique for 8 bytes, specialised to 4:
  the installed prefix only grows over `DrainSpur`, not-yet-drained
  bytes still read the start memory, and an exclusion-checked
  four-drain installs exactly the `write32` footprint bytes with
  read-back. `DrainSchritt`/`DrainSpur` and the permission framing
  are reused unchanged; only the entry list (`fpEintraege32`), the
  group guard (`FpGruppe32`/`FpFremdFrei32`) and the footprint
  (`fpFuss32`) are the 32-bit specialisation. -/

/-- Dropping `k < 4` entries exposes byte `k` at the head: the drain
    order is fixed oldest-first. -/
theorem fp32Eintraege_kopf (a : Adresse) (v : Wort) (k : Nat)
    (hk : k < 4) :
    (fpEintraege32 a v).drop k =
      ⟨addrOff a k, wortByte v k⟩ ::
        (fpEintraege32 a v).drop (k + 1) := by
  have h4 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases h4 with rfl | rfl | rfl | rfl <;> rfl

/-- Every 32-bit footprint address lies in the 32-bit footprint. -/
theorem fpFuss32_mem_offset (a : Adresse) (k : Nat) (hk : k < 4) :
    addrOff a k ∈ fpFuss32 a := by
  have h4 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  unfold fpFuss32
  rcases h4 with rfl | rfl | rfl | rfl
  · exact List.mem_map_of_mem (by decide)
  · exact List.mem_map_of_mem (by decide)
  · exact List.mem_map_of_mem (by decide)
  · exact List.mem_map_of_mem (by decide)

/-- INSTALLED PREFIX (32-bit): from `k` installed bytes the trace
    only advances the installed prefix. The group pins the start
    buffer, the trace the prefix, the exclusion every foreign step,
    membership the state. -/
theorem fp32_drain_installiert_aux (c : Nat) (a : Adresse) (v : Wort)
    (s sN : TSOZustand) (t : List TSOZustand)
    (hspur : DrainSpur c s sN t) :
    ∀ (hstoer : ∀ x ∈ t, FpFremdFrei32 x c a) (k : Nat), k ≤ 4 →
      ∀ (hbuf : s.puffer c = (fpEintraege32 a v).drop k)
        (hmem : ∀ j : Nat, j < k → s.mem.bytes (addrOff a j) = wortByte v j)
        (x : TSOZustand), x ∈ t →
        ∃ k' : Nat, k ≤ k' ∧ k' ≤ 4 ∧
          x.puffer c = (fpEintraege32 a v).drop k' ∧
          (∀ j : Nat, j < k' → x.mem.bytes (addrOff a j) = wortByte v j) := by
  induction hspur with
  | leer s =>
    intro hstoer k hk hbuf hmem x hx
    simp at hx
    subst hx
    exact ⟨k, Nat.le_refl k, hk, hbuf, hmem⟩
  | schritt s s' sN t hstep hrest iht =>
    intro hstoer k hk hbuf hmem x hx
    have hstoer' : ∀ y ∈ t, FpFremdFrei32 y c a := by
      intro y hy
      exact hstoer y (by simp only [List.mem_cons]; exact Or.inr hy)
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hxt
    · exact ⟨k, Nat.le_refl k, hk, hbuf, hmem⟩
    · match hstep with
      | .eigen hfl =>
        have hk4 : k < 4 := by
          have h4 : k = 4 ∨ k < 4 := by omega
          rcases h4 with rfl | hk4
          · have hempty : s.puffer c = [] := by
              rw [hbuf]
              rfl
            rw [flush_leer s c hempty] at hfl
            cases hfl
          · exact hk4
        have hhead : s.puffer c =
            ⟨addrOff a k, wortByte v k⟩ ::
              (fpEintraege32 a v).drop (k + 1) := by
          rw [hbuf]
          exact fp32Eintraege_kopf a v k hk4
        have hbuf' : s'.puffer c = (fpEintraege32 a v).drop (k + 1) :=
          flush_entfernt_kopf s s' c hfl _ _ hhead
        have hneu : s'.mem.bytes (addrOff a k) = wortByte v k :=
          flush_schreibt_kopf s s' c hfl _ _ hhead
        have hmem' : ∀ j : Nat, j < k + 1 →
            s'.mem.bytes (addrOff a j) = wortByte v j := by
          intro j hj
          by_cases hjk : j = k
          · subst hjk
            exact hneu
          · have hj8 : j < 8 := by omega
            have hk8 : k < 8 := by omega
            have hne : addrOff a j ≠
                (⟨addrOff a k, wortByte v k⟩ : TSOEintrag).addr :=
              addrOff_ne8 hj8 hk8 hjk
            have hframe : s'.mem.bytes (addrOff a j) =
                s.mem.bytes (addrOff a j) :=
              flush_rahmen s s' c hfl _ _ hhead _ hne
            rw [hframe]
            exact hmem j (by omega)
        obtain ⟨k', hkk', hk'4, hbufN, hmemN⟩ :=
          iht hstoer' (k + 1) (by omega) hbuf' hmem' x hxt
        exact ⟨k', by omega, hk'4, hbufN, hmemN⟩
      | .fremdSpülen d hne hfl =>
        have hown : s'.puffer c = s.puffer c :=
          flush_anderer_kern s s' d hfl (Ne.symm hne)
        have hbuf' : s'.puffer c = (fpEintraege32 a v).drop k := by
          rw [hown, hbuf]
        match hpd : s.puffer d with
        | [] =>
          have hnone : flushKern s d = none := flush_leer s d hpd
          rw [hnone] at hfl
          cases hfl
        | e :: rest =>
          have hmem_e : e ∈ s.puffer d := hpd ▸ by simp
          have hff : FpFremdFrei32 s c a := hstoer s (by simp)
          have hout : e.addr ∉ fpFuss32 a := hff d hne e hmem_e
          have hmem' : ∀ j : Nat, j < k →
              s'.mem.bytes (addrOff a j) = wortByte v j := by
            intro j hj
            have hj4 : j < 4 := by omega
            have hmem_foot : addrOff a j ∈ fpFuss32 a :=
              fpFuss32_mem_offset a j hj4
            have hne_j : addrOff a j ≠ e.addr := by
              intro heq
              exact hout (heq ▸ hmem_foot)
            have hframe : s'.mem.bytes (addrOff a j) =
                s.mem.bytes (addrOff a j) :=
              flush_rahmen s s' d hfl e rest hpd _ hne_j
            rw [hframe]
            exact hmem j hj
          obtain ⟨k', hkk', hk'4, hbufN, hmemN⟩ :=
            iht hstoer' k hk hbuf' hmem' x hxt
          exact ⟨k', hkk', hk'4, hbufN, hmemN⟩
      | .fremdAusgabe d e hne hissue =>
        have hown : s'.puffer c = s.puffer c :=
          issue_anderer_kern s s' d e.addr e.wert hissue (Ne.symm hne)
        have hbuf' : s'.puffer c = (fpEintraege32 a v).drop k := by
          rw [hown, hbuf]
        have hmem' : ∀ j : Nat, j < k →
            s'.mem.bytes (addrOff a j) = wortByte v j := by
          intro j hj
          have hframe : s'.mem.bytes (addrOff a j) =
              s.mem.bytes (addrOff a j) :=
            issue_kein_speicher s s' d e.addr e.wert hissue _
          rw [hframe]
          exact hmem j hj
        obtain ⟨k', hkk', hk'4, hbufN, hmemN⟩ :=
          iht hstoer' k hk hbuf' hmem' x hxt
        exact ⟨k', hkk', hk'4, hbufN, hmemN⟩

/-- UNINSTALLED PREFIX PRESERVED (32-bit): from `k` installed
    bytes the not-yet-drained footprint bytes still read the start
    memory. Own flushes install a different byte, foreign flushes
    avoid the footprint, foreign issues are silent. -/
theorem fp32_drain_uninstalliert_aux (c : Nat) (a : Adresse) (v : Wort)
    (s sN : TSOZustand) (t : List TSOZustand)
    (hspur : DrainSpur c s sN t) :
    ∀ (hstoer : ∀ x ∈ t, FpFremdFrei32 x c a) (k : Nat), k ≤ 4 →
      ∀ (hbuf : s.puffer c = (fpEintraege32 a v).drop k)
        (x : TSOZustand), x ∈ t →
        ∃ k' : Nat, k ≤ k' ∧ k' ≤ 4 ∧
          x.puffer c = (fpEintraege32 a v).drop k' ∧
          (∀ j : Nat, k' ≤ j → j < 4 →
            x.mem.bytes (addrOff a j) = s.mem.bytes (addrOff a j)) := by
  induction hspur with
  | leer s =>
    intro hstoer k hk hbuf x hx
    simp at hx
    subst hx
    exact ⟨k, Nat.le_refl k, hk, hbuf, fun _ _ _ => rfl⟩
  | schritt s s' sN t hstep hrest iht =>
    intro hstoer k hk hbuf x hx
    have hstoer' : ∀ y ∈ t, FpFremdFrei32 y c a := by
      intro y hy
      exact hstoer y (by simp only [List.mem_cons]; exact Or.inr hy)
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hxt
    · exact ⟨k, Nat.le_refl k, hk, hbuf, fun _ _ _ => rfl⟩
    · match hstep with
      | .eigen hfl =>
        have hk4 : k < 4 := by
          have h4 : k = 4 ∨ k < 4 := by omega
          rcases h4 with rfl | hk4
          · have hempty : s.puffer c = [] := by
              rw [hbuf]
              rfl
            rw [flush_leer s c hempty] at hfl
            cases hfl
          · exact hk4
        have hhead : s.puffer c =
            ⟨addrOff a k, wortByte v k⟩ ::
              (fpEintraege32 a v).drop (k + 1) := by
          rw [hbuf]
          exact fp32Eintraege_kopf a v k hk4
        have hbuf' : s'.puffer c = (fpEintraege32 a v).drop (k + 1) :=
          flush_entfernt_kopf s s' c hfl _ _ hhead
        have hframe : ∀ j : Nat, k + 1 ≤ j → j < 4 →
            s'.mem.bytes (addrOff a j) = s.mem.bytes (addrOff a j) := by
          intro j hj hj4
          have hj8 : j < 8 := by omega
          have hk8 : k < 8 := by omega
          have hne : addrOff a j ≠
              (⟨addrOff a k, wortByte v k⟩ : TSOEintrag).addr :=
            addrOff_ne8 hj8 hk8 (by omega)
          exact flush_rahmen s s' c hfl _ _ hhead _ hne
        obtain ⟨k', hkk', hk'4, hbufN, hrestM⟩ :=
          iht hstoer' (k + 1) (by omega) hbuf' x hxt
        refine ⟨k', by omega, hk'4, hbufN, ?_⟩
        intro j hj hj4
        rw [hrestM j hj hj4]
        exact hframe j (by omega) hj4
      | .fremdSpülen d hne hfl =>
        have hown : s'.puffer c = s.puffer c :=
          flush_anderer_kern s s' d hfl (Ne.symm hne)
        have hbuf' : s'.puffer c = (fpEintraege32 a v).drop k := by
          rw [hown, hbuf]
        match hpd : s.puffer d with
        | [] =>
          have hnone : flushKern s d = none := flush_leer s d hpd
          rw [hnone] at hfl
          cases hfl
        | e :: rest =>
          have hmem_e : e ∈ s.puffer d := hpd ▸ by simp
          have hff : FpFremdFrei32 s c a := hstoer s (by simp)
          have hout : e.addr ∉ fpFuss32 a := hff d hne e hmem_e
          have hframe : ∀ j : Nat, k ≤ j → j < 4 →
              s'.mem.bytes (addrOff a j) = s.mem.bytes (addrOff a j) := by
            intro j _ hj4
            have hmem_foot : addrOff a j ∈ fpFuss32 a :=
              fpFuss32_mem_offset a j hj4
            have hne_j : addrOff a j ≠ e.addr := by
              intro heq
              exact hout (heq ▸ hmem_foot)
            exact flush_rahmen s s' d hfl e rest hpd _ hne_j
          obtain ⟨k', hkk', hk'4, hbufN, hrestM⟩ :=
            iht hstoer' k hk hbuf' x hxt
          refine ⟨k', hkk', hk'4, hbufN, ?_⟩
          intro j hj hj4
          rw [hrestM j hj hj4]
          exact hframe j (by omega) hj4
      | .fremdAusgabe d e hne hissue =>
        have hown : s'.puffer c = s.puffer c :=
          issue_anderer_kern s s' d e.addr e.wert hissue (Ne.symm hne)
        have hbuf' : s'.puffer c = (fpEintraege32 a v).drop k := by
          rw [hown, hbuf]
        have hframe : ∀ j : Nat, k ≤ j → j < 4 →
            s'.mem.bytes (addrOff a j) = s.mem.bytes (addrOff a j) := by
          intro j _ _
          exact issue_kein_speicher s s' d e.addr e.wert hissue _
        obtain ⟨k', hkk', hk'4, hbufN, hrestM⟩ :=
          iht hstoer' k hk hbuf' x hxt
        refine ⟨k', hkk', hk'4, hbufN, ?_⟩
        intro j hj hj4
        rw [hrestM j hj hj4]
        exact hframe j (by omega) hj4

/-- FULL INTERMEDIATE PREFIX (32-bit): every visited state is
    exactly a stated prefix -- buffer suffix, installed bytes from
    the word, not-yet-drained bytes still from the start memory. -/
theorem fp32_drain_voll (c : Nat) (a : Adresse) (v : Wort)
    (s sN : TSOZustand) (t : List TSOZustand)
    (hgrp : FpGruppe32 s c a v)
    (hspur : DrainSpur c s sN t)
    (hstoer : ∀ x ∈ t, FpFremdFrei32 x c a)
    (x : TSOZustand) (hx : x ∈ t) :
    ∃ k' : Nat, k' ≤ 4 ∧
      x.puffer c = (fpEintraege32 a v).drop k' ∧
      (∀ j : Nat, j < k' → x.mem.bytes (addrOff a j) = wortByte v j) ∧
      (∀ j : Nat, k' ≤ j → j < 4 →
        x.mem.bytes (addrOff a j) = s.mem.bytes (addrOff a j)) := by
  obtain ⟨hbufl, _hff⟩ := hgrp
  have hbase : s.puffer c = (fpEintraege32 a v).drop 0 := by
    rw [hbufl]
    rfl
  obtain ⟨k1, _h01, hk14, hbuf1, hinst⟩ :=
    fp32_drain_installiert_aux c a v s sN t hspur hstoer 0
      (Nat.zero_le 4) hbase (fun j hj => absurd hj (by omega)) x hx
  obtain ⟨k2, _hk0, hk24, hbuf2, hrest⟩ :=
    fp32_drain_uninstalliert_aux c a v s sN t hspur hstoer 0
      (Nat.zero_le 4) hbase x hx
  have hkk : k1 = k2 := by
    rw [hbuf1] at hbuf2
    have hlen := congrArg (fun l => (l.length)) hbuf2
    rw [List.length_drop, List.length_drop, fpEintraege32_laenge] at hlen
    omega
  subst hkk
  exact ⟨k1, hk14, hbuf1, hinst, hrest⟩

/-- Four-byte read permission survives the whole drain: every step
    preserves the permission maps. -/
theorem fp32_lesbarN_gleich (s s' : TSOZustand)
    (hperm : s'.mem.lesbar = s.mem.lesbar) (a : Adresse) (n : Nat) :
    lesbarN s'.mem a n = lesbarN s.mem a n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show (lesbarN s'.mem a n && s'.mem.lesbar (addrOff a n)) =
      (lesbarN s.mem a n && s.mem.lesbar (addrOff a n))
    rw [ih, hperm]

/-- Drain readability: the four footprint bytes stay readable on
    every visited state. -/
theorem fp32_drain_lesbarN_aux (c : Nat) (a : Adresse)
    (s sN : TSOZustand) (t : List TSOZustand)
    (hspur : DrainSpur c s sN t) :
    ∀ (_hles : lesbarN s.mem a 4 = true) (x : TSOZustand),
      x ∈ t → lesbarN x.mem a 4 = true := by
  induction hspur with
  | leer s =>
    intro hles x hx
    simp at hx
    subst hx
    exact hles
  | schritt s s' sN t hstep _ iht =>
    intro hles x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hles
    · have hperm := drain_schritt_berechtigungen c s s' hstep
      have hles' : lesbarN s'.mem a 4 = true := by
        have e : lesbarN s'.mem a 4 = lesbarN s.mem a 4 :=
          fp32_lesbarN_gleich s s' hperm.1 a 4
        rw [e]
        exact hles
      exact iht hles' x hx

/-- DRAIN EQUALS WRITE-BYTES ON THE FOOTPRINT (32-bit): an
    exclusion-checked four-drain installs exactly the `writeBytesN`
    footprint bytes for `n = 4`. -/
theorem fp32DrainFuss_gleich_schreibbytesN (s sN : TSOZustand)
    (t : List TSOZustand) (c : Nat) (a : Adresse) (v : Wort)
    (hgrp : FpGruppe32 s c a v)
    (hspur : DrainSpur c s sN t) (hend : sN ∈ t)
    (hleer : sN.puffer c = [])
    (hstoer : ∀ x ∈ t, FpFremdFrei32 x c a) :
    ∀ j : Nat, j < 4 →
      sN.mem.bytes (addrOff a j) = writeBytesN s.mem a v 4 (addrOff a j) := by
  obtain ⟨k', hk'4, hbufN, hinst, _hrest⟩ :=
    fp32_drain_voll c a v s sN t hgrp hspur hstoer sN hend
  have hempty : (fpEintraege32 a v).drop k' = [] := by
    rw [← hbufN, hleer]
  have hlen0 := congrArg List.length hempty
  simp only [List.length_drop, fpEintraege32_laenge,
    List.length_nil] at hlen0
  have hk_eq : k' = 4 := by omega
  subst hk_eq
  intro j hj
  rw [hinst j hj]
  have hhit := writeBytesN_hit s.mem a v 4 j hj (by decide)
  show wortByte v j = writeBytesN s.mem a v 4 (addrOff a j)
  exact hhit.symm

/-- GROUPED READ-BACK (32-bit): an exclusion-checked drain from the
    exact four-entry group reads back the low 32 bits unsplit. -/
theorem fp32_gruppe_liest_zurueck (s2 sN : TSOZustand)
    (t : List TSOZustand) (c : Nat) (a : Adresse) (v : Wort)
    (hgrp : FpGruppe32 s2 c a v) (hles : lesbarN s2.mem a 4 = true)
    (hspur : DrainSpur c s2 sN t) (hend : sN ∈ t)
    (hleer : sN.puffer c = []) (hstoer : ∀ x ∈ t, FpFremdFrei32 x c a) :
    read32 sN.mem a = some (BitVec.ofNat 64 (v.toNat % 4294967296)) := by
  obtain ⟨hbufl, _hff⟩ := hgrp
  have hbase : s2.puffer c = (fpEintraege32 a v).drop 0 := by
    rw [hbufl]
    rfl
  obtain ⟨k, _hk0, _hk4, hbufN, hinst⟩ :=
    fp32_drain_installiert_aux c a v s2 sN t hspur hstoer 0
      (Nat.zero_le 4) hbase
      (fun j hj => absurd hj (by omega)) sN hend
  have hlen0 : (sN.puffer c).length = 0 := by
    rw [hleer]
    rfl
  rw [hbufN, List.length_drop, fpEintraege32_laenge] at hlen0
  have hk_eq : k = 4 := by omega
  subst hk_eq
  have hlesN : lesbarN sN.mem a 4 = true :=
    fp32_drain_lesbarN_aux c a s2 sN t hspur hles sN hend
  have b0 : sN.mem.bytes a = wortByte v 0 := by
    have hhit := hinst 0 (by decide)
    rwa [addrOff_null a] at hhit
  have b1 : sN.mem.bytes (addrOff a 1) = wortByte v 1 :=
    hinst 1 (by decide)
  have b2 : sN.mem.bytes (addrOff a 2) = wortByte v 2 :=
    hinst 2 (by decide)
  have b3 : sN.mem.bytes (addrOff a 3) = wortByte v 3 :=
    hinst 3 (by decide)
  unfold read32
  rw [if_pos hlesN]
  congr 1
  apply BitVec.eq_of_toNat_eq
  show (BitVec.ofNat 64 ((sN.mem.bytes a).toNat +
    (sN.mem.bytes (addrOff a 1)).toNat * 256 +
    (sN.mem.bytes (addrOff a 2)).toNat * 65536 +
    (sN.mem.bytes (addrOff a 3)).toNat * 16777216)).toNat =
    (BitVec.ofNat 64 (v.toNat % 4294967296)).toNat
  rw [b0, b1, b2, b3]
  unfold wortByte
  simp only [BitVec.toNat_ofNat]
  omega

/-- DRAIN EQUALS `write32` (32-bit): an exclusion-checked four-drain
    agrees with the successful `write32` on the whole footprint and
    reads back the low 32 bits. -/
theorem fp32DrainGleichWrite32 (s sN : TSOZustand)
    (t : List TSOZustand) (c : Nat) (a : Adresse) (v : Wort)
    (m' : Speicher)
    (hgrp : FpGruppe32 s c a v) (hles : lesbarN s.mem a 4 = true)
    (hspur : DrainSpur c s sN t) (hend : sN ∈ t)
    (hleer : sN.puffer c = [])
    (hstoer : ∀ x ∈ t, FpFremdFrei32 x c a)
    (hwr : write32 s.mem a v = some m') :
    (∀ j : Nat, j < 4 →
      sN.mem.bytes (addrOff a j) = m'.bytes (addrOff a j)) ∧
      read32 sN.mem a = some (BitVec.ofNat 64 (v.toNat % 4294967296)) := by
  have hfoot := fp32DrainFuss_gleich_schreibbytesN s sN t c a v
    hgrp hspur hend hleer hstoer
  have hread := fp32_gruppe_liest_zurueck s sN t c a v
    hgrp hles hspur hend hleer hstoer
  have hmeq : ∀ x : Adresse,
      m'.bytes x = writeBytesN s.mem a v 4 x := by
    unfold write32 at hwr
    by_cases hc : schreibbarN s.mem a 4 = true
    · rw [if_pos hc] at hwr
      cases hwr
      intro x
      rfl
    · rw [if_neg hc] at hwr
      cases hwr
  refine ⟨?_, hread⟩
  intro j hj
  rw [hfoot j hj, hmeq]

/-- STMXCSR DRAIN EQUALS `write32`: the accepted STMXCSR issue (four
    buffered bytes of `mxcsrSpeicherWort`) drains to exactly the
    `write32` of that word. Issue half IS lane 1211
    (`fpDispSt_ist_ausgabe32`, `fpDispSt_gruppe`); drain half is above. -/
theorem fp32StDrain_gleich (sN : TSOZustand)
    (t : List TSOZustand) (c : Nat) (a : Adresse) (w : MXCSR)
    (m m' : HwMaschine)
    (hempty : m.puffer c = [])
    (hfrei : FpFremdFrei32 (tsoAnsicht m) c a)
    (hiss : fpDispMxcsrAusgabe m c a w = some m')
    (hles : lesbarN (tsoAnsicht m').mem a 4 = true)
    (hspur : DrainSpur c (tsoAnsicht m') sN t) (hend : sN ∈ t)
    (hleer : sN.puffer c = [])
    (hstoer : ∀ x ∈ t, FpFremdFrei32 x c a)
    (mW : Speicher)
    (hwr : write32 (tsoAnsicht m').mem a (mxcsrSpeicherWort w) =
      some mW) :
    (∀ j : Nat, j < 4 →
      sN.mem.bytes (addrOff a j) = mW.bytes (addrOff a j)) ∧
      read32 sN.mem a =
        some (BitVec.ofNat 64 ((mxcsrSpeicherWort w).toNat % 4294967296)) := by
  have hgrp := fpDispSt_gruppe m m' c a w hempty hfrei hiss
  exact fp32DrainGleichWrite32 (tsoAnsicht m') sN t c a
    (mxcsrSpeicherWort w) mW hgrp hles hspur hend hleer hstoer hwr

/-- MOVSS-STORE DRAIN EQUALS `write32`: the accepted MOVSS-store
    issue (four buffered bytes of the source low single) drains to
    exactly the `write32` of that word. Issue half IS lane 1211
    (`fpDispMovss_ist_ausgabe32`); the group is the accepted
    `fpCtrlAusgabe32_gruppe`; drain half is above. -/
theorem fp32MovssDrain_gleich (sN : TSOZustand)
    (t : List TSOZustand) (c : Nat) (a : Adresse)
    (f : XmmDatei) (src : XmmReg)
    (m m' : HwMaschine)
    (hempty : m.puffer c = [])
    (hfrei : FpFremdFrei32 (tsoAnsicht m) c a)
    (hiss : fpDispMovssAusgabe m c a f src = some m')
    (hles : lesbarN (tsoAnsicht m').mem a 4 = true)
    (hspur : DrainSpur c (tsoAnsicht m') sN t) (hend : sN ∈ t)
    (hleer : sN.puffer c = [])
    (hstoer : ∀ x ∈ t, FpFremdFrei32 x c a)
    (mW : Speicher)
    (hwr : write32 (tsoAnsicht m').mem a
      (BitVec.setWidth 64 (xmmTief32 f src)) = some mW) :
    (∀ j : Nat, j < 4 →
      sN.mem.bytes (addrOff a j) = mW.bytes (addrOff a j)) ∧
      read32 sN.mem a = some (BitVec.ofNat 64
        ((BitVec.setWidth 64 (xmmTief32 f src)).toNat % 4294967296)) := by
  have hgrp : FpGruppe32 (tsoAnsicht m') c a
      (BitVec.setWidth 64 (xmmTief32 f src)) := by
    unfold fpDispMovssAusgabe at hiss
    exact fpCtrlAusgabe32_gruppe m m' c a _ hempty hfrei hiss
  exact fp32DrainGleichWrite32 (tsoAnsicht m') sN t c a
    (BitVec.setWidth 64 (xmmTief32 f src)) mW hgrp hles hspur hend
    hleer hstoer hwr

/-! ## 4. Forwarding to the owner, old view for the foreign core.

  After a 32-bit store issue the owner observes every stored byte
  (the accepted `fpCtrlWeiterleitung32`, lifted through the
  adapter); a core with an empty buffer still reads canonical
  memory (no foreign forwarding). -/

/-- FORWARDING, ALL FOUR BYTES: after core `c` stores word `v` at
    readable `a` from an empty own buffer, core `c` observes every
    stored byte through the family adapter. -/
theorem fp32Weiterleitung_eigen (m m' : HwMaschine) (c : Nat)
    (a : Adresse) (v : Wort)
    (hempty : m.puffer c = [])
    (hrd0 : m.mem.lesbar (addrOff a 0) = true)
    (hrd1 : m.mem.lesbar (addrOff a 1) = true)
    (hrd2 : m.mem.lesbar (addrOff a 2) = true)
    (hrd3 : m.mem.lesbar (addrOff a 3) = true)
    (h : fpStoreAdapter.schritt m c (.speichere32 a v) = some m') :
    loadByte (tsoAnsicht m') c (addrOff a 0) = some (wortByte v 0) ∧
    loadByte (tsoAnsicht m') c (addrOff a 1) = some (wortByte v 1) ∧
    loadByte (tsoAnsicht m') c (addrOff a 2) = some (wortByte v 2) ∧
    loadByte (tsoAnsicht m') c (addrOff a 3) = some (wortByte v 3) :=
  fpCtrlWeiterleitung32 m m' c a v hempty hrd0 hrd1 hrd2 hrd3 h

/-- NO FOREIGN FORWARDING: a core with an empty buffer reads
    canonical memory, whatever another core buffered. -/
theorem fp32Leer_liest_speicher (m' : HwMaschine) (d : Nat)
    (a : Adresse)
    (hleer : (tsoAnsicht m').puffer d = [])
    (hrd : (tsoAnsicht m').mem.lesbar a = true) :
    loadByte (tsoAnsicht m') d a = some ((tsoAnsicht m').mem.bytes a) := by
  have hmiss : neuestens ((tsoAnsicht m').puffer d) a = none := by
    rw [hleer]
    rfl
  exact load_ohne_eintrag _ _ _ hmiss hrd

/-! ## 5. Tearing refusals: partial buffers and crossed groups.

  A partial four-entry buffer is no `FpGruppe32` (the accepted
  `fpGruppe32_teilwort`), a foreign footprint entry breaks it (the
  accepted `fpGruppe32_fremd`), and -- the new case -- a 4-byte
  store whose footprint shares a byte with an in-flight foreign
  8-byte `WortGruppe` crosses that group's boundary and tears: the
  overlapping foreign entry sits inside `fpFuss32`, so no 32-bit
  group forms. The byte drain never consults alignment, so this
  structural overlap -- not an alignment gate -- is the refusal. -/

/-- A 4-byte store crossing an in-flight foreign 8-byte group tears:
    the shared byte's foreign entry lies inside the 32-bit
    footprint, so no `FpGruppe32` forms. Every premise is used: the
    8-byte group pins the foreign buffer, the indices the shared
    byte, the crossing equation its two names. -/
theorem fp32KreuztGruppe_kein_gruppe (s : TSOZustand) (c d : Nat)
    (a b : Adresse) (v8 v4 : Wort) (hne : d ≠ c)
    (hgrp8 : WortGruppe s d b v8)
    (j k : Nat) (hj : j < 4) (hk : k < 8)
    (hkreuz : addrOff a j = addrOff b k) :
    ¬ FpGruppe32 s c a v4 := by
  obtain ⟨hbuf8, _hff⟩ := hgrp8
  have heintrag : (⟨addrOff b k, wortByte v8 k⟩ : TSOEintrag) ∈
      s.puffer d := by
    rw [hbuf8]
    have h8 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨
        k = 6 ∨ k = 7 := by omega
    rcases h8 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [wortEintraege]
  have hfuss : addrOff b k ∈ fpFuss32 a := by
    rw [← hkreuz]
    exact fpFuss32_mem_offset a j hj
  exact fpGruppe32_fremd s c a v4 d hne _ heintrag hfuss

/-! ## 6. Joint witness: two cores, buffered store, forward, drain.

  Core 0 buffers the `3.0f32` word at the data cell through the
  family adapter (no canonical byte moves); core 0 forwards it
  while core 1 still reads zero; core 0 drains the four entries
  into shared memory (bytes 2 and 3 go `0` to `0x40`), observed
  from both cores with the accepted `write32` read-back. Beside it
  stand the planted refusals: a partial buffer is no group, a
  misaligned store straddling an in-flight 8-byte group tears, an
  empty drain and a guarded store refuse. Every observation below
  is a closed decidable evaluation, except the drain equations,
  which fire the generic induction of §3. -/

/-- Witness bytes: zeroed everywhere. -/
def fp32WitBytes (_ : Adresse) : Byte := BitVec.ofNat 8 0

/-- Witness data permission: eight bytes at 8192. -/
def fp32WitDaten (a : Adresse) : Bool :=
  decide (8192 ≤ a.toNat ∧ a.toNat < 8200)

/-- Witness shared memory: zeroed bytes, data RW, nothing executable. -/
def fp32WitMem : Speicher :=
  { bytes := fp32WitBytes, lesbar := fp32WitDaten,
    schreibbar := fp32WitDaten, ausfuehrbar := fun _ => false }

/-- Witness registers: all zero on both cores. -/
def fp32WitReg : Register → Wort := fun _ => BitVec.ofNat 64 0

/-- Witness cores: both idle; the family touches memory, not registers. -/
def fp32WitKern : Nat → HwKern
  | _ => ⟨fp32WitReg, zeugeFlags, BitVec.ofNat 64 4096,
      (fun _ => BitVec.ofNat 128 0), kontextReset⟩

/-- Witness start machine: shared memory, two cores, empty buffers,
    full silicon with OS vector state. -/
def fp32WitM0 : HwMaschine :=
  ⟨fp32WitMem, fp32WitKern, fun _ => [], basisHw, fun _ => basisBereit⟩

/-- Witness store address and value (`3.0f32` as a target word). -/
def fp32WitAdr : Adresse := BitVec.ofNat 64 8192
def fp32WitWert : Wort := BitVec.ofNat 64 0x40400000

/-- The witness machine is well-formed: full silicon admits all. -/
theorem fp32WitM0_wf : HwWf fp32WitM0 := by
  intro c f _
  cases f <;> rfl

/-- Core 0 buffers the word through the family adapter. -/
def fp32WitPush : Option HwMaschine :=
  fpStoreAdapter.schritt fp32WitM0 0
    (.speichere32 fp32WitAdr fp32WitWert)

/-- Buffered entry count on core 0 after the store. -/
def fp32WitBufLen : Option Nat :=
  match fp32WitPush with
  | some m1 => some (m1.puffer 0).length
  | none => none

/-- Third footprint byte right after the store (still zero). -/
def fp32WitMemStill : Option Byte :=
  match fp32WitPush with
  | some m1 => some (m1.mem.bytes (addrOff fp32WitAdr 2))
  | none => none

/-- Core 0 observes its own third footprint byte (forwarding). -/
def fp32WitLoadEigen : Option (Option Byte) :=
  match fp32WitPush with
  | some m1 =>
    some (loadByte (tsoAnsicht m1) 0 (addrOff fp32WitAdr 2))
  | none => none

/-- Core 1 observes the old third footprint byte (no forwarding). -/
def fp32WitLoadFremd : Option (Option Byte) :=
  match fp32WitPush with
  | some m1 =>
    some (loadByte (tsoAnsicht m1) 1 (addrOff fp32WitAdr 2))
  | none => none

/-- The store buffers exactly four entries on core 0. -/
theorem fp32Wit_puffer4 : fp32WitBufLen = some 4 := by
  decide

/-- The store leaves the third footprint byte at zero. -/
theorem fp32Wit_mem_still :
    fp32WitMemStill = some (BitVec.ofNat 8 0) := by
  decide

/-- Forwarding on the reached run: core 0 reads its own `0x40`. -/
theorem fp32Wit_weiterleitung :
    fp32WitLoadEigen = some (some (BitVec.ofNat 8 0x40)) := by
  decide

/-- No foreign forwarding on the reached run: core 1 reads zero. -/
theorem fp32Wit_fremd_alt :
    fp32WitLoadFremd = some (some (BitVec.ofNat 8 0)) := by
  decide

/-- Pushed TSO state: core 0 carries exactly the four entries,
    core 1 is empty. -/
def fp32WitS0 : TSOZustand :=
  ⟨fp32WitMem, fun d =>
    if d = 0 then fpEintraege32 fp32WitAdr fp32WitWert else []⟩

/-- After own flush 1: byte 0 installed. -/
def fp32WitS1 : TSOZustand :=
  ⟨{ fp32WitMem with bytes := fun x =>
      if (x = addrOff fp32WitAdr 0) then wortByte fp32WitWert 0
      else fp32WitMem.bytes x },
    pufferSetze fp32WitS0.puffer 0
      ((fpEintraege32 fp32WitAdr fp32WitWert).drop 1)⟩

/-- After own flush 2: bytes 0-1 installed. -/
def fp32WitS2 : TSOZustand :=
  ⟨{ fp32WitS1.mem with bytes := fun x =>
      if (x = addrOff fp32WitAdr 1) then wortByte fp32WitWert 1
      else fp32WitS1.mem.bytes x },
    pufferSetze fp32WitS1.puffer 0
      ((fpEintraege32 fp32WitAdr fp32WitWert).drop 2)⟩

/-- After own flush 3: bytes 0-2 installed. -/
def fp32WitS3 : TSOZustand :=
  ⟨{ fp32WitS2.mem with bytes := fun x =>
      if (x = addrOff fp32WitAdr 2) then wortByte fp32WitWert 2
      else fp32WitS2.mem.bytes x },
    pufferSetze fp32WitS2.puffer 0
      ((fpEintraege32 fp32WitAdr fp32WitWert).drop 3)⟩

/-- After own flush 4: all bytes installed, own buffer empty. -/
def fp32WitS4 : TSOZustand :=
  ⟨{ fp32WitS3.mem with bytes := fun x =>
      if (x = addrOff fp32WitAdr 3) then wortByte fp32WitWert 3
      else fp32WitS3.mem.bytes x },
    pufferSetze fp32WitS3.puffer 0
      ((fpEintraege32 fp32WitAdr fp32WitWert).drop 4)⟩

/-- Each recorded flush computes as claimed. -/
theorem fp32Wit_step1 : flushKern fp32WitS0 0 = some fp32WitS1 := by
  rfl

theorem fp32Wit_step2 : flushKern fp32WitS1 0 = some fp32WitS2 := by
  rfl

theorem fp32Wit_step3 : flushKern fp32WitS2 0 = some fp32WitS3 := by
  rfl

theorem fp32Wit_step4 : flushKern fp32WitS3 0 = some fp32WitS4 := by
  rfl

/-- Foreign buffers start empty off core 0. -/
theorem fp32WitS0_fremd_leer :
    ∀ d : Nat, d ≠ 0 → fp32WitS0.puffer d = [] := by
  intro d hne
  show (if d = 0 then fpEintraege32 fp32WitAdr fp32WitWert
    else []) = []
  rw [if_neg hne]

/-- Foreign-buffer emptiness down the whole drain. -/
theorem fp32WitS1_fremd_leer :
    ∀ d : Nat, d ≠ 0 → fp32WitS1.puffer d = [] :=
  fremd_leer_eigen_erhalten fp32WitS0 fp32WitS1 fp32Wit_step1
    fp32WitS0_fremd_leer

theorem fp32WitS2_fremd_leer :
    ∀ d : Nat, d ≠ 0 → fp32WitS2.puffer d = [] :=
  fremd_leer_eigen_erhalten fp32WitS1 fp32WitS2 fp32Wit_step2
    fp32WitS1_fremd_leer

theorem fp32WitS3_fremd_leer :
    ∀ d : Nat, d ≠ 0 → fp32WitS3.puffer d = [] :=
  fremd_leer_eigen_erhalten fp32WitS2 fp32WitS3 fp32Wit_step3
    fp32WitS2_fremd_leer

theorem fp32WitS4_fremd_leer :
    ∀ d : Nat, d ≠ 0 → fp32WitS4.puffer d = [] :=
  fremd_leer_eigen_erhalten fp32WitS3 fp32WitS4 fp32Wit_step4
    fp32WitS3_fremd_leer

/-- Empty foreign buffers satisfy the 32-bit exclusion check. -/
theorem fp32FremdFrei32_aus_leer (s : TSOZustand) (c : Nat)
    (b : Adresse)
    (hleer : ∀ d : Nat, d ≠ c → s.puffer d = []) :
    FpFremdFrei32 s c b := by
  intro d hne e he
  rw [hleer d hne] at he
  simp at he

/-- Every visited state is foreign-free at the grouped footprint. -/
theorem fp32Wit_ff0 : FpFremdFrei32 fp32WitS0 0 fp32WitAdr :=
  fp32FremdFrei32_aus_leer fp32WitS0 0 _ fp32WitS0_fremd_leer

theorem fp32Wit_ff1 : FpFremdFrei32 fp32WitS1 0 fp32WitAdr :=
  fp32FremdFrei32_aus_leer fp32WitS1 0 _ fp32WitS1_fremd_leer

theorem fp32Wit_ff2 : FpFremdFrei32 fp32WitS2 0 fp32WitAdr :=
  fp32FremdFrei32_aus_leer fp32WitS2 0 _ fp32WitS2_fremd_leer

theorem fp32Wit_ff3 : FpFremdFrei32 fp32WitS3 0 fp32WitAdr :=
  fp32FremdFrei32_aus_leer fp32WitS3 0 _ fp32WitS3_fremd_leer

theorem fp32Wit_ff4 : FpFremdFrei32 fp32WitS4 0 fp32WitAdr :=
  fp32FremdFrei32_aus_leer fp32WitS4 0 _ fp32WitS4_fremd_leer

/-- Each recorded step is an own-flush drain step. -/
theorem fp32Wit_e1 : DrainSchritt 0 fp32WitS0 fp32WitS1 :=
  .eigen fp32Wit_step1

theorem fp32Wit_e2 : DrainSchritt 0 fp32WitS1 fp32WitS2 :=
  .eigen fp32Wit_step2

theorem fp32Wit_e3 : DrainSchritt 0 fp32WitS2 fp32WitS3 :=
  .eigen fp32Wit_step3

theorem fp32Wit_e4 : DrainSchritt 0 fp32WitS3 fp32WitS4 :=
  .eigen fp32Wit_step4

/-- The full four-drain trace. -/
theorem fp32Wit_spur : DrainSpur 0 fp32WitS0 fp32WitS4
    [fp32WitS0, fp32WitS1, fp32WitS2, fp32WitS3, fp32WitS4] :=
  .schritt _ _ _ _ fp32Wit_e1 (.schritt _ _ _ _ fp32Wit_e2
    (.schritt _ _ _ _ fp32Wit_e3
      (.schritt _ _ _ _ fp32Wit_e4 (.leer fp32WitS4))))

/-- The drain end is visited. -/
theorem fp32Wit_hend :
    fp32WitS4 ∈
      [fp32WitS0, fp32WitS1, fp32WitS2, fp32WitS3, fp32WitS4] := by
  simp

/-- The drain ends with an empty own buffer. -/
theorem fp32Wit_hempty : fp32WitS4.puffer 0 = [] := by
  rfl

/-- The witness start satisfies the grouping check. -/
theorem fp32Wit_hgrp :
    FpGruppe32 fp32WitS0 0 fp32WitAdr fp32WitWert :=
  ⟨rfl, fp32Wit_ff0⟩

/-- The witness start reads the grouped footprint. -/
theorem fp32Wit_hles :
    lesbarN fp32WitS0.mem fp32WitAdr 4 = true := by
  decide

/-- The whole trace is foreign-free at the grouped footprint. -/
theorem fp32Wit_hstoer :
    ∀ x ∈ [fp32WitS0, fp32WitS1, fp32WitS2, fp32WitS3, fp32WitS4],
      FpFremdFrei32 x 0 fp32WitAdr := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl
  · exact fp32Wit_ff0
  · exact fp32Wit_ff1
  · exact fp32Wit_ff2
  · exact fp32Wit_ff3
  · exact fp32Wit_ff4

/-- The pushed buffer IS the drain start buffer, and no pushed byte
    moved: the TSO drain starts exactly where the machine push
    ends. -/
theorem fp32Wit_push_gleich_start (m1 : HwMaschine)
    (hpush : fp32WitPush = some m1) :
    (tsoAnsicht m1).puffer 0 = fp32WitS0.puffer 0 ∧
      (∀ x : Adresse, (tsoAnsicht m1).mem.bytes x =
        fp32WitS0.mem.bytes x) := by
  have hb := fpStoreSpeichere_puffer fp32WitM0 0 fp32WitAdr
    fp32WitWert m1 hpush
  have hempty' : fp32WitM0.puffer 0 = [] := rfl
  refine ⟨?_, ?_⟩
  · show m1.puffer 0 = fp32WitS0.puffer 0
    rw [hb, hempty']
    rfl
  · intro x
    have hm := fpStoreSpeichere_kein_speicher fp32WitM0 0
      fp32WitAdr fp32WitWert m1 hpush x
    exact hm

/-- The drained memory, as the accepted `write32` writes it. -/
def fp32WitNach : Speicher :=
  { fp32WitMem with bytes := writeBytesN fp32WitMem fp32WitAdr fp32WitWert 4 }

/-- The `write32` of the stored word succeeds on the witness start. -/
theorem fp32Wit_hwr :
    write32 fp32WitS0.mem fp32WitAdr fp32WitWert =
      some fp32WitNach := by
  have hc : schreibbarN fp32WitMem fp32WitAdr 4 = true := by
    decide
  have e : fp32WitS0.mem = fp32WitMem := rfl
  rw [e]
  show write32 fp32WitMem fp32WitAdr fp32WitWert = some fp32WitNach
  unfold write32
  unfold fp32WitNach
  rw [if_pos hc]

/-- GENERIC FIRE on the witness: the drained bytes are the
    `write32` bytes, and the low 32 bits read back. -/
theorem fp32Wit_feuer :
    (∀ j : Nat, j < 4 →
      fp32WitS4.mem.bytes (addrOff fp32WitAdr j) =
        fp32WitNach.bytes (addrOff fp32WitAdr j)) ∧
      read32 fp32WitS4.mem fp32WitAdr =
        some (BitVec.ofNat 64
          (fp32WitWert.toNat % 4294967296)) :=
  fp32DrainGleichWrite32 fp32WitS0 fp32WitS4 _ 0 fp32WitAdr
    fp32WitWert fp32WitNach fp32Wit_hgrp fp32Wit_hles
    fp32Wit_spur fp32Wit_hend fp32Wit_hempty fp32Wit_hstoer
    fp32Wit_hwr

/-- The drain is a reached TSO run from its start state. -/
theorem fp32Wit_erreichbar :
    TSOErreichbar fp32WitS0 fp32WitS4 :=
  drain_spur_erreichbar 0 fp32WitS0 fp32WitS4 _ fp32Wit_spur

/-- The third footprint byte starts zeroed. -/
theorem fp32Wit_anfang_null :
    fp32WitS0.mem.bytes (addrOff fp32WitAdr 2) =
      BitVec.ofNat 8 0 := by
  decide

/-- After the drain core 1 observes the new third byte. -/
theorem fp32Wit_fremd_neu :
    loadByte fp32WitS4 1 (addrOff fp32WitAdr 2) =
      some (BitVec.ofNat 8 0x40) := by
  decide

/-- The drain observably changes memory. -/
theorem fp32Wit_aendert :
    fp32WitS0.mem.bytes (addrOff fp32WitAdr 2) ≠
      fp32WitS4.mem.bytes (addrOff fp32WitAdr 2) := by
  decide

/-! ## 7. Refusal witnesses: partial, crossed, guarded, dark, empty.

  A two-entry buffer is no 32-bit group (tearing); a misaligned
  4-byte store at 8198 straddling the in-flight 8-byte group at
  8192 (shared bytes 8198, 8199) tears; a write-protected store
  and a dark observation refuse; an empty drain refuses. -/

/-- Partial buffer: two of four bytes. -/
def fp32WitTeil : TSOZustand :=
  ⟨fp32WitMem, fun d =>
    if d = 0 then (fpEintraege32 fp32WitAdr fp32WitWert).take 2
    else []⟩

/-- Tearing refuses the group: two of four bytes are no word. -/
theorem fp32Wit_teil_kein_gruppe :
    ¬ FpGruppe32 fp32WitTeil 0 fp32WitAdr fp32WitWert := by
  apply fpGruppe32_teilwort
  decide

/-- The crossed 8-byte group base (aligned) and the misaligned
    4-byte store address straddling it. -/
def fp32WitKreuzB : Adresse := BitVec.ofNat 64 8192
def fp32WitKreuzA : Adresse := BitVec.ofNat 64 8198
def fp32WitKreuzW8 : Wort := BitVec.ofNat 64 7

/-- Overlap state: core 1 holds a full 8-byte group at 8192 while
    core 0 would store four bytes at 8198. -/
def fp32WitKreuz : TSOZustand :=
  ⟨fp32WitMem, fun d =>
    if d = 1 then wortEintraege fp32WitKreuzB fp32WitKreuzW8 else []⟩

/-- The foreign 8-byte group is established. -/
theorem fp32Wit_kreuz_hgrp8 :
    WortGruppe fp32WitKreuz 1 fp32WitKreuzB fp32WitKreuzW8 := by
  refine ⟨rfl, ?_⟩
  intro d hne e hm
  have hbuf : fp32WitKreuz.puffer d = [] := by
    show (if d = 1 then wortEintraege fp32WitKreuzB fp32WitKreuzW8
      else []) = []
    rw [if_neg hne]
  rw [hbuf] at hm
  cases hm

/-- The footprints share a byte: `8198 + 0 = 8192 + 6`. -/
theorem fp32Wit_kreuz :
    addrOff fp32WitKreuzA 0 = addrOff fp32WitKreuzB 6 := by
  decide

/-- The crossed store tears: no 32-bit group forms. -/
theorem fp32Wit_kreuz_kein_gruppe :
    ¬ FpGruppe32 fp32WitKreuz 0 fp32WitKreuzA fp32WitWert :=
  fp32KreuztGruppe_kein_gruppe fp32WitKreuz 0 1 fp32WitKreuzA
    fp32WitKreuzB fp32WitKreuzW8 fp32WitWert (by decide)
    fp32Wit_kreuz_hgrp8 0 6 (by decide) (by decide) fp32Wit_kreuz

/-- Guard witness memory: nothing is writable. -/
def fp32WitGuardMem : Speicher :=
  { bytes := fp32WitBytes, lesbar := fp32WitDaten,
    schreibbar := fun _ => false, ausfuehrbar := fun _ => false }

/-- Guard witness machine: same cores, write-protected memory. -/
def fp32WitGuardM0 : HwMaschine :=
  ⟨fp32WitGuardMem, fp32WitKern, fun _ => [], basisHw,
    fun _ => basisBereit⟩

/-- The guard denies the first footprint byte. -/
theorem fp32Wit_guard_dicht :
    fp32WitGuardM0.mem.schreibbar (addrOff fp32WitAdr 0) = false := by
  decide

/-- Guard store refuses on the witness. -/
theorem fp32Wit_guard_verweigert :
    fpStoreAdapter.schritt fp32WitGuardM0 0
      (.speichere32 fp32WitAdr fp32WitWert) = none :=
  fpStoreSpeichere_wache _ _ _ _ fp32Wit_guard_dicht

/-- Dark witness memory: nothing is readable. -/
def fp32WitDarkMem : Speicher :=
  { bytes := fp32WitBytes, lesbar := fun _ => false,
    schreibbar := fp32WitDaten, ausfuehrbar := fun _ => false }

/-- Dark witness machine: same cores, unreadable memory. -/
def fp32WitDarkM0 : HwMaschine :=
  ⟨fp32WitDarkMem, fp32WitKern, fun _ => [], basisHw,
    fun _ => basisBereit⟩

/-- The dark page denies the third footprint byte. -/
theorem fp32Wit_dark_dicht :
    (tsoAnsicht fp32WitDarkM0).mem.lesbar
      (addrOff fp32WitAdr 2) = false := by
  decide

/-- Dark observation refuses on the witness. -/
theorem fp32Wit_dark_verweigert :
    fpStoreAdapter.schritt fp32WitDarkM0 0
      (.beobachte (addrOff fp32WitAdr 2)) = none :=
  fpStoreBeobachte_dunkel _ _ _ fp32Wit_dark_dicht

/-- Empty own drain refuses on the witness start machine. -/
theorem fp32Wit_eigen_leer_verweigert :
    fpStoreAdapter.schritt fp32WitM0 0 .eigenSpuele = none :=
  fpStoreEigen_leer_verweigert _ _ rfl

/-! ## 8. Joint witness: a reached non-degenerate two-core run.

  The adapter buffers `3.0f32` with owner-only forwarding over
  unchanged shared memory; the TSO drain starts exactly there and
  installs the accepted `write32` footprint with read-back,
  observed from both cores while observably changing memory --
  beside the tearing/overlap/guard/dark/empty refusals. -/

/-- JOINT WITNESS (32-bit FP store drain on the coherent machine). -/
theorem fp32StoreDrain_zeuge :
    HwWf fp32WitM0 ∧
      fp32WitBufLen = some 4 ∧
      fp32WitMemStill = some (BitVec.ofNat 8 0) ∧
      fp32WitLoadEigen = some (some (BitVec.ofNat 8 0x40)) ∧
      fp32WitLoadFremd = some (some (BitVec.ofNat 8 0)) ∧
      (∀ m1 : HwMaschine, fp32WitPush = some m1 →
        (tsoAnsicht m1).puffer 0 = fp32WitS0.puffer 0 ∧
        (∀ x : Adresse, (tsoAnsicht m1).mem.bytes x =
          fp32WitS0.mem.bytes x)) ∧
      (∀ j : Nat, j < 4 →
        fp32WitS4.mem.bytes (addrOff fp32WitAdr j) =
          fp32WitNach.bytes (addrOff fp32WitAdr j)) ∧
      read32 fp32WitS4.mem fp32WitAdr =
        some (BitVec.ofNat 64
          (fp32WitWert.toNat % 4294967296)) ∧
      loadByte fp32WitS4 1 (addrOff fp32WitAdr 2) =
        some (BitVec.ofNat 8 0x40) ∧
      TSOErreichbar fp32WitS0 fp32WitS4 ∧
      fp32WitS0.mem.bytes (addrOff fp32WitAdr 2) ≠
        fp32WitS4.mem.bytes (addrOff fp32WitAdr 2) ∧
      ¬ FpGruppe32 fp32WitTeil 0 fp32WitAdr fp32WitWert ∧
      ¬ FpGruppe32 fp32WitKreuz 0 fp32WitKreuzA fp32WitWert ∧
      fpStoreAdapter.schritt fp32WitGuardM0 0
        (.speichere32 fp32WitAdr fp32WitWert) = none ∧
      fpStoreAdapter.schritt fp32WitDarkM0 0
        (.beobachte (addrOff fp32WitAdr 2)) = none ∧
      fpStoreAdapter.schritt fp32WitM0 0 .eigenSpuele = none := by
  exact ⟨fp32WitM0_wf, fp32Wit_puffer4, fp32Wit_mem_still,
    fp32Wit_weiterleitung, fp32Wit_fremd_alt,
    fp32Wit_push_gleich_start, fp32Wit_feuer.1, fp32Wit_feuer.2,
    fp32Wit_fremd_neu, fp32Wit_erreichbar, fp32Wit_aendert,
    fp32Wit_teil_kein_gruppe, fp32Wit_kreuz_kein_gruppe,
    fp32Wit_guard_verweigert, fp32Wit_dark_verweigert,
    fp32Wit_eigen_leer_verweigert⟩

/- CUTS: what is proved here, and what is not.

   Proved here, over the reused accepted vocabulary
   (`HardwareExecution`: `HwMaschine`/`HwSchritt`/`HwAdapter`/`HwWf`/
   `issueListe`/`setTso`; `HwFpControl`: `fpCtrlAusgabe32`/
   `fpEintraege32`/`FpGruppe32`/`FpFremdFrei32`/`fpFuss32`;
   `HwFpDispatch`: `fpDispMxcsrAusgabe`/`fpDispMovssAusgabe`/
   `fpDispSt_gruppe`; `HwDrainGeneric` technique specialised;
   `WordAccessGrouping`: `DrainSchritt`/`DrainSpur`/
   `WortGruppe`; `Speicher`: `read32`/`write32`/`writeBytesN`;
   `TSO`: `issueByte`/`loadByte`/`flushKern`):
   - family events `FpStoreEreignis` and the adapter
     `fpStoreAdapter` with `HwWf` preservation, buffer agreement
     (exactly the four canonical entries, no canonical byte moves),
     own drains as the accepted flush and machine flush events,
     silent observations, and empty-drain/guard/dark refusals;
   - the 4-byte drain induction: installed prefix
     (`fp32_drain_installiert_aux`), uninstalled preservation
     (`fp32_drain_uninstalliert_aux`), joined
     (`fp32_drain_voll`), readability (`fp32_drain_lesbarN_aux`),
     footprint equals `writeBytesN` for `n = 4`, grouped
     read-back, and DRAIN EQUALS `write32` with read-back
     (`fp32DrainGleichWrite32`);
   - STMXCSR and MOVSS-store corollaries: the accepted issue
     halves (lane 1211) drain to exactly the `write32` of the
     accepted stored words (`mxcsrSpeicherWort`,
     `setWidth 64 (xmmTief32 f src)`);
   - owner-only forwarding (`fp32Weiterleitung_eigen`,
     `fp32Leer_liest_speicher`);
   - tearing refusals: partial buffers (accepted
     `fpGruppe32_teilwort`), foreign entries (accepted
     `fpGruppe32_fremd`), and the new crossed-group case
     (`fp32KreuztGruppe_kein_gruppe`: a 4-byte store sharing a
     byte with an in-flight foreign 8-byte group tears);
   - joint non-degenerate two-core witness
     (`fp32StoreDrain_zeuge`): adapter push of `3.0f32` with
     owner-only forwarding, the TSO drain starting exactly there,
     `write32` footprint with read-back observed from both cores,
     an observably changed byte, reachability, beside all
     refusals.
   NOT proved here, and not claimed:
   - No hardware correspondence: encodings are the accepted
     canonical subsets with self-consistency only, not x86 truth.
     The byte drain never consults alignment, so the crossed-group
     refusal is structural overlap, not an alignment gate; no
     4-byte no-wrap (`OhneUmbruch` is 8-byte) is stated.
   - No per-access target-to-W/GX simulation and no whole-word
     atomicity beyond the `FpGruppe32`-guarded byte drains; no
     source/IR/ABI/loader/entry/budget link; timing, power,
     interrupts and faults beyond the carried divide halt are
     absent.
   - Silicon provenance is cited from the family files, never
     restated; the Intel SDM extracts are provenance, not proofs.
-/

#print axioms fpStoreAdapter_wf
#print axioms fpStoreSpeichere_puffer
#print axioms fpStoreSpeichere_kein_speicher
#print axioms fpStoreEigen_ist_flush
#print axioms fpStoreEigen_ist_schritt
#print axioms fpStoreBeobachte_still
#print axioms fpStoreEigen_leer_verweigert
#print axioms fpStoreSpeichere_wache
#print axioms fpStoreBeobachte_dunkel
#print axioms fp32Eintraege_kopf
#print axioms fpFuss32_mem_offset
#print axioms fp32_drain_installiert_aux
#print axioms fp32_drain_uninstalliert_aux
#print axioms fp32_drain_voll
#print axioms fp32_lesbarN_gleich
#print axioms fp32_drain_lesbarN_aux
#print axioms fp32DrainFuss_gleich_schreibbytesN
#print axioms fp32_gruppe_liest_zurueck
#print axioms fp32DrainGleichWrite32
#print axioms fp32StDrain_gleich
#print axioms fp32MovssDrain_gleich
#print axioms fp32Weiterleitung_eigen
#print axioms fp32Leer_liest_speicher
#print axioms fp32KreuztGruppe_kein_gruppe
#print axioms fp32WitM0_wf
#print axioms fp32Wit_puffer4
#print axioms fp32Wit_weiterleitung
#print axioms fp32Wit_push_gleich_start
#print axioms fp32Wit_hgrp
#print axioms fp32Wit_spur
#print axioms fp32Wit_hwr
#print axioms fp32Wit_feuer
#print axioms fp32Wit_erreichbar
#print axioms fp32Wit_teil_kein_gruppe
#print axioms fp32Wit_kreuz_kein_gruppe
#print axioms fp32Wit_guard_verweigert
#print axioms fp32Wit_dark_verweigert
#print axioms fp32Wit_eigen_leer_verweigert
#print axioms fp32StoreDrain_zeuge

end Gabbro.Grammatik.X86
