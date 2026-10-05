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
import Grammatik.X86.HardwareExecution
import Grammatik.X86.HwFpControl
import Grammatik.X86.HwFpDispatch
import Grammatik.X86.HwDrainGeneric
import Grammatik.X86.WordAccessGrouping

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

/- CUTS: skeleton plus adapter duties; induction, forwarding, refusals open.
-/

#print axioms FpStoreEreignis
#print axioms fpStoreAdapter

end Gabbro.Grammatik.X86
