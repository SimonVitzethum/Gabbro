/-
  File:      Grammatik/X86/HwKapsteinTso.lean
  Subject:   Capstone: every classified union step projects to the TSO
             store-buffer model.

  Lane 1295: projection `kapTso` of `HwMaschine` to the TSO-only machine
  (memory, per-core buffers, forwarding) and the refinement that underlies
  every per-access bridge. The base step classifies exactly (silent,
  single issue, single flush, forward-read observation); word/drain/fwd/
  stack family steps reach via `TSOErreichbar`. Remaining tags are FINDINGs.
  Every accepted definition is reused unchanged, never redefined.
-/
import Grammatik.X86.Hw.Kapstein.HwKapstein
namespace Gabbro.Grammatik.X86

/-- Projection of the coherent machine to the TSO-only machine:
    shared memory plus per-core store buffers. -/
def kapTso (m : HwMaschine) : TSOZustand :=
  tsoAnsicht m

/-- Core-data updates leave the projection unchanged. -/
theorem kapTso_setKernDaten (m : HwMaschine) (c : Nat) (k : HwKern) :
    kapTso (setKernDaten m c k) = kapTso m := by
  rfl

/-- Memory/buffer updates project to the successor state. -/
theorem kapTso_setTso (m : HwMaschine) (s : TSOZustand) :
    kapTso (setTso m s) = s := by
  cases s with
  | mk mem puffer => rfl

/-- Re-embedded core successors leave the projection unchanged. -/
theorem kapTso_setKernVonFp (m : HwMaschine) (c : Nat) (t' : FpZustand) :
    kapTso (setKernVonFp m c t') = kapTso m := by
  rfl

/-- Every coherent base step classifies on the TSO projection with its
    footprint named: register and fault steps are silent, loads observe
    with forwarding, issues are single `issueByte` events, drains are
    single `flushKern` events with the buffer head named. -/
theorem kap_basis_tso_klass (m m' : HwMaschine) (e : HwEreignis)
    (h : HwSchritt m m' e) :
    (∃ c i, e = .regAusf c i ∧ kapTso m' = kapTso m)
    ∨ (∃ c a v, e = .leseBeob c a v ∧ kapTso m' = kapTso m
      ∧ loadByte (kapTso m) c a = some v)
    ∨ (∃ c a v s', e = .schreibAusgabe c a v
      ∧ issueByte (kapTso m) c a v = some s' ∧ kapTso m' = s')
    ∨ (∃ c e0 s', e = .spülung c e0
      ∧ flushKern (kapTso m) c = some s' ∧ kapTso m' = s'
      ∧ (m.puffer c).head? = some e0)
    ∨ (∃ c, e = .verweigert c ∧ kapTso m' = kapTso m) := by
  cases h with
  | reg c i t' hstep hmem =>
    exact Or.inl ⟨c, i, rfl, kapTso_setKernVonFp _ c t'⟩
  | lade c a v hload =>
    exact Or.inr (Or.inl ⟨c, a, v, rfl, rfl, hload⟩)
  | gibAus c a v s' hissue =>
    exact Or.inr (Or.inr (Or.inl ⟨c, a, v, s', rfl, hissue,
      kapTso_setTso _ s'⟩))
  | spüle c e0 s' hflush hkopf =>
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨c, e0, s', rfl, hflush,
      kapTso_setTso _ s', hkopf⟩)))
  | fehler c hfetch =>
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨c, rfl, rfl⟩)))

/-- Reachability is transitive: used to chain single-issue steps. -/
theorem kapTso_erreichbar_trans (s0 s1 s2 : TSOZustand)
    (h1 : TSOErreichbar s0 s1) (h2 : TSOErreichbar s1 s2) :
    TSOErreichbar s0 s2 := by
  induction h2 with
  | start => exact h1
  | schritt _ hstep ih => exact .schritt ih hstep

/-- A single TSO step reaches. -/
theorem kapTso_schritt_erreichbar (s s' : TSOZustand)
    (h : TSOSchritt s s') : TSOErreichbar s s' := by
  exact .schritt .start h

/-- A folded issue list reaches: induction over the entry list,
    chaining single `issue` steps. -/
theorem kapTso_issueListe_erreichbar (s : TSOZustand) (c : Nat)
    (l : List TSOEintrag) (s' : TSOZustand)
    (h : issueListe s c l = some s') : TSOErreichbar s s' := by
  induction l generalizing s s' with
  | nil =>
    simp [issueListe] at h
    subst h
    exact .start
  | cons e rest ih =>
    unfold issueListe at h
    cases h1 : issueByte s c e.addr e.wert with
    | none => rw [h1] at h; cases h
    | some s1 =>
      rw [h1] at h
      have hstep : TSOSchritt s s1 := .issue s s1 c e.addr e.wert h1
      have hreach1 : TSOErreichbar s s1 :=
        kapTso_schritt_erreichbar s s1 hstep
      have hreach2 : TSOErreichbar s1 s' := ih s1 s' h
      exact kapTso_erreichbar_trans s s1 s' hreach1 hreach2

/-- A buffered word store reaches through the projection: eight byte
    issues, never a direct memory write. -/
theorem kapTso_wortAusgabe_erreichbar (m : HwMaschine) (c : Nat)
    (a : Adresse) (v : Wort) (m' : HwMaschine)
    (h : hwWortAusgabe m c a v = some m') :
    TSOErreichbar (kapTso m) (kapTso m') := by
  unfold hwWortAusgabe at h
  cases h1 : issueListe (tsoAnsicht m) c (wortEintraege a v) with
  | none => rw [h1] at h; cases h
  | some s' =>
    rw [h1] at h
    cases h
    have hr : TSOErreichbar (tsoAnsicht m) s' :=
      kapTso_issueListe_erreichbar (tsoAnsicht m) c
        (wortEintraege a v) s' h1
    have heq : kapTso (setTso m s') = s' := kapTso_setTso m s'
    rw [heq]
    exact hr

/-- Every whole-word adapter step reaches through the projection:
    stores buffer eight bytes, drains flush one oldest entry. -/
theorem kap_wort_tso (m : HwMaschine) (c : Nat) (e : HwWortZugriff)
    (m' : HwMaschine)
    (h : adapterWort1147.schritt m c e = some m') :
    TSOErreichbar (kapTso m) (kapTso m') := by
  cases e with
  | wortAusgabe a v =>
    rw [adapterWort1147_ausgabe] at h
    exact kapTso_wortAusgabe_erreichbar m c a v m' h
  | wortSpuelung =>
    rw [adapterWort1147_spuelung] at h
    cases hfl : flushKern (tsoAnsicht m) c with
    | none => rw [hfl] at h; cases h
    | some s' =>
      rw [hfl] at h
      cases h
      rw [kapTso_setTso]
      exact kapTso_schritt_erreichbar _ _
        (.flush _ s' c hfl)

/-- Every generic drain adapter step reaches through the projection:
    word stores buffer, own/foreign drains flush, foreign issues issue,
    observations are silent. -/
theorem kap_drain_tso (m : HwMaschine) (c : Nat) (e : DrainEreignis)
    (m' : HwMaschine)
    (h : drainAdapter.schritt m c e = some m') :
    TSOErreichbar (kapTso m) (kapTso m') := by
  cases e with
  | speichere a v =>
    have had : drainAdapter.schritt m c (.speichere a v) =
        hwWortAusgabe m c a v := rfl
    rw [had] at h
    exact kapTso_wortAusgabe_erreichbar m c a v m' h
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
      rw [hh] at h; cases h
      rw [kapTso_setTso]
      exact kapTso_schritt_erreichbar _ _
        (.flush _ s' c hfl)
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
      rw [hh] at h; cases h
      rw [kapTso_setTso]
      exact kapTso_schritt_erreichbar _ _
        (.flush _ s' d hfl)
  | fremdAusgabe d f =>
    cases hfl : issueByte (tsoAnsicht m) d f.addr f.wert with
    | none =>
      have hh : drainAdapter.schritt m c (.fremdAusgabe d f) = none := by
        show (match issueByte (tsoAnsicht m) d f.addr f.wert with
          | some s' => some (setTso m s') | none => none) = none
        rw [hfl]
      rw [hh] at h; cases h
    | some s' =>
      have hh : drainAdapter.schritt m c (.fremdAusgabe d f) =
          some (setTso m s') := by
        show (match issueByte (tsoAnsicht m) d f.addr f.wert with
          | some s' => some (setTso m s') | none => none) = _
        rw [hfl]
      rw [hh] at h; cases h
      rw [kapTso_setTso]
      exact kapTso_schritt_erreichbar _ _
        (.issue _ s' d f.addr f.wert hfl)
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
      rw [hh] at h
      cases h
      exact .start

/-- Every generic forwarding adapter step reaches through the projection:
    word stores buffer, observations are silent. -/
theorem kap_fwd_tso (m : HwMaschine) (c : Nat) (e : FwdEreignis)
    (m' : HwMaschine)
    (h : fwdAdapter.schritt m c e = some m') :
    TSOErreichbar (kapTso m) (kapTso m') := by
  cases e with
  | speichere a v =>
    have had : fwdAdapter.schritt m c (.speichere a v) =
        hwWortAusgabe m c a v := rfl
    rw [had] at h
    exact kapTso_wortAusgabe_erreichbar m c a v m' h
  | beobachte a =>
    cases hl : stapelLadeWort (tsoAnsicht m) c a with
    | none =>
      have hh : fwdAdapter.schritt m c (.beobachte a) = none := by
        show (match stapelLadeWort (tsoAnsicht m) c a with
          | some _ => some m | none => none) = none
        rw [hl]
      rw [hh] at h; cases h
    | some w =>
      have hh : fwdAdapter.schritt m c (.beobachte a) = some m := by
        show (match stapelLadeWort (tsoAnsicht m) c a with
          | some _ => some m | none => none) = some m
        rw [hl]
      rw [hh] at h
      cases h
      exact .start

/-- A buffered stack push reaches through the projection. -/
theorem kap_stapelPush_erreichbar (m : HwMaschine) (c : Nat) (v : Wort)
    (m' : HwMaschine) (h : stapelPush m c v = some m') :
    TSOErreichbar (kapTso m) (kapTso m') := by
  have heq : stapelPush m c v =
      hwWortAusgabe m c (stapelSlot m c) v := rfl
  rw [heq] at h
  exact kapTso_wortAusgabe_erreichbar m c (stapelSlot m c) v m' h

/-- A buffered call spill reaches through the projection. -/
theorem kap_stapelCall_erreichbar (m : HwMaschine) (c : Nat) (ret : Wort)
    (m' : HwMaschine) (h : stapelCall m c ret = some m') :
    TSOErreichbar (kapTso m) (kapTso m') := by
  have heq : stapelCall m c ret =
      hwWortAusgabe m c (stapelSlot m c) ret := rfl
  rw [heq] at h
  exact kapTso_wortAusgabe_erreichbar m c (stapelSlot m c) ret m' h

/-- Every stack adapter step reaches through the projection: pushes and
    aligned calls buffer a word, pop/ret observations are silent. -/
theorem kap_stapel_tso (m : HwMaschine) (c : Nat) (e : StapelEreignis)
    (m' : HwMaschine)
    (h : stapelAdapter.schritt m c e = some m') :
    TSOErreichbar (kapTso m) (kapTso m') := by
  cases e with
  | push v =>
    have had : stapelAdapter.schritt m c (.push v) =
        stapelPush m c v := rfl
    rw [had] at h
    exact kap_stapelPush_erreichbar m c v m' h
  | ruf ret =>
    by_cases ha : rufAlignOk (projZustand m c) = true
    · have hh : stapelAdapter.schritt m c (.ruf ret) =
          stapelCall m c ret := by
        show (if rufAlignOk (projZustand m c) then stapelCall m c ret
          else none) = _
        rw [if_pos ha]
      rw [hh] at h
      exact kap_stapelCall_erreichbar m c ret m' h
    · have hh : stapelAdapter.schritt m c (.ruf ret) = none := by
        show (if rufAlignOk (projZustand m c) then stapelCall m c ret
          else none) = _
        rw [if_neg ha]
      rw [hh] at h; cases h
  | pop a =>
    cases hl : stapelLadeWort (tsoAnsicht m) c a with
    | none =>
      have hh : stapelAdapter.schritt m c (.pop a) = none := by
        show (match stapelLadeWort (tsoAnsicht m) c a with
          | some _ => some m | none => none) = none
        rw [hl]
      rw [hh] at h; cases h
    | some w =>
      have hh : stapelAdapter.schritt m c (.pop a) = some m := by
        show (match stapelLadeWort (tsoAnsicht m) c a with
          | some _ => some m | none => none) = some m
        rw [hl]
      rw [hh] at h
      cases h
      exact .start
  | ret a =>
    cases hl : stapelLadeWort (tsoAnsicht m) c a with
    | none =>
      have hh : stapelAdapter.schritt m c (.ret a) = none := by
        show (match stapelLadeWort (tsoAnsicht m) c a with
          | some _ => some m | none => none) = none
        rw [hl]
      rw [hh] at h; cases h
    | some w =>
      have hh : stapelAdapter.schritt m c (.ret a) = some m := by
        show (match stapelLadeWort (tsoAnsicht m) c a with
          | some _ => some m | none => none) = some m
        rw [hl]
      rw [hh] at h
      cases h
      exact .start

/-- Every coherent base step reaches through the projection: silent
    steps reuse `.start`, issues and drains use one TSO step. -/
theorem kap_basis_reichbar (m m' : HwMaschine) (e : HwEreignis)
    (h : HwSchritt m m' e) :
    TSOErreichbar (kapTso m) (kapTso m') := by
  rcases kap_basis_tso_klass m m' e h with
    ⟨c, i, _, heq⟩ | ⟨c, a, v, _, heq, _⟩
      | ⟨c, a, v, s', _, hissue, heq⟩
      | ⟨c, e0, s', _, hflush, heq, _⟩ | ⟨c, _, heq⟩
  · rw [heq]; exact .start
  · rw [heq]; exact .start
  · rw [heq]
    exact kapTso_schritt_erreichbar _ _
      (.issue _ s' c a v hissue)
  · rw [heq]
    exact kapTso_schritt_erreichbar _ _
      (.flush _ s' c hflush)
  · rw [heq]; exact .start

/-- A classified basis union step reaches through the projection. -/
theorem kap_union_basis_tso (m m' : HwMaschine) (e : HwEreignis)
    (h : HwVollSchritt m m' (KapEreignis.basis e)) :
    TSOErreichbar (kapTso m) (kapTso m') := by
  cases h with
  | basis _ hstep => exact kap_basis_reichbar _ _ _ hstep

/-- A classified whole-word union step reaches through the projection. -/
theorem kap_union_wort_tso (m m' : HwMaschine) (c : Nat)
    (e : HwWortZugriff)
    (h : HwVollSchritt m m' (KapEreignis.wort c e)) :
    TSOErreichbar (kapTso m) (kapTso m') := by
  cases h with
  | wort _ _ heq => exact kap_wort_tso _ c e _ heq

/-- A classified drain union step reaches through the projection. -/
theorem kap_union_drain_tso (m m' : HwMaschine) (c : Nat)
    (e : DrainEreignis)
    (h : HwVollSchritt m m' (KapEreignis.drain c e)) :
    TSOErreichbar (kapTso m) (kapTso m') := by
  cases h with
  | drain _ _ heq => exact kap_drain_tso _ c e _ heq

/-- A classified forwarding union step reaches through the projection. -/
theorem kap_union_fwd_tso (m m' : HwMaschine) (c : Nat)
    (e : FwdEreignis)
    (h : HwVollSchritt m m' (KapEreignis.fwd c e)) :
    TSOErreichbar (kapTso m) (kapTso m') := by
  cases h with
  | fwd _ _ heq => exact kap_fwd_tso _ c e _ heq

/-- A classified stack union step reaches through the projection. -/
theorem kap_union_stapel_tso (m m' : HwMaschine) (c : Nat)
    (e : StapelEreignis)
    (h : HwVollSchritt m m' (KapEreignis.stapel c e)) :
    TSOErreichbar (kapTso m) (kapTso m') := by
  cases h with
  | stapel _ _ heq => exact kap_stapel_tso _ c e _ heq

/-- Joint summary: all five classified tags reach through the TSO
    projection. Each premise is used by its own leg. -/
theorem kap_fuenf_tso :
    (∀ (m m' : HwMaschine) (e : HwEreignis),
      HwVollSchritt m m' (.basis e) →
        TSOErreichbar (kapTso m) (kapTso m'))
    ∧ (∀ (m m' : HwMaschine) (c : Nat) (e : HwWortZugriff),
      HwVollSchritt m m' (.wort c e) →
        TSOErreichbar (kapTso m) (kapTso m'))
    ∧ (∀ (m m' : HwMaschine) (c : Nat) (e : DrainEreignis),
      HwVollSchritt m m' (.drain c e) →
        TSOErreichbar (kapTso m) (kapTso m'))
    ∧ (∀ (m m' : HwMaschine) (c : Nat) (e : FwdEreignis),
      HwVollSchritt m m' (.fwd c e) →
        TSOErreichbar (kapTso m) (kapTso m'))
    ∧ (∀ (m m' : HwMaschine) (c : Nat) (e : StapelEreignis),
      HwVollSchritt m m' (.stapel c e) →
        TSOErreichbar (kapTso m) (kapTso m')) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro m m' e h
    exact kap_union_basis_tso m m' e h
  · intro m m' c e h
    exact kap_union_wort_tso m m' c e h
  · intro m m' c e h
    exact kap_union_drain_tso m m' c e h
  · intro m m' c e h
    exact kap_union_fwd_tso m m' c e h
  · intro m m' c e h
    exact kap_union_stapel_tso m m' c e h

/-- The basis observation through the projection: the exhibited base
    union step forwards byte zero at the stack slot. -/
theorem kapTso_basis_beob (c : Nat) (a : Adresse) (v : Byte)
    (hstep : HwSchritt stapelWitM0 stapelWitM0
      (.leseBeob c a v)) :
    loadByte (kapTso stapelWitM0) c a = some v := by
  rcases kap_basis_tso_klass _ _ _ hstep with
    ⟨c1, i, heq, _⟩ | ⟨c1, a1, v1, heq, _, hld⟩
    | ⟨c1, a1, v1, s', heq, _, _⟩
    | ⟨c1, e0, s', heq, _, _, _⟩ | ⟨c1, heq, _⟩
  · cases heq
  · cases heq
    exact hld
  · cases heq
  · cases heq
  · cases heq

/-- Joint TSO witness: four exhibited union steps reach through the
    projection, the base observation reads zero through it, and the
    two-core non-degeneracy (owner-only forwarding 42, foreign stale 0,
    drain installs 42) holds on the same TSO model. -/
theorem kapTso_zeuge :
    (∃ m1, HwVollSchritt stapelWitM0 m1
      (KapEreignis.wort 0
        (.wortAusgabe (stapelSlot stapelWitM0 0) stapelWitWort))
      ∧ TSOErreichbar (kapTso stapelWitM0) (kapTso m1))
    ∧ (∃ m1, HwVollSchritt stapelWitM0 m1
      (KapEreignis.stapel 0 (.push stapelWitWort))
      ∧ TSOErreichbar (kapTso stapelWitM0) (kapTso m1))
    ∧ (∃ m1, HwVollSchritt drainWitM0 m1
      (KapEreignis.drain 0 (.speichere drainWitAdr drainWitWort))
      ∧ TSOErreichbar (kapTso drainWitM0) (kapTso m1))
    ∧ (∃ m1, HwVollSchritt witFwdM0 m1
      (KapEreignis.fwd 0 (.speichere witFwdAdr witFwdWort))
      ∧ TSOErreichbar (kapTso witFwdM0) (kapTso m1))
    ∧ HwVollSchritt stapelWitM0 stapelWitM0
      (KapEreignis.basis
        (.leseBeob 0 stapelWitSlotAddr (BitVec.ofNat 8 0)))
    ∧ loadByte (kapTso stapelWitM0) 0 stapelWitSlotAddr =
        some (BitVec.ofNat 8 0)
    ∧ hwWitLoadEigen = some (some (BitVec.ofNat 8 42))
    ∧ hwWitLoadFremd = some (some (BitVec.ofNat 8 0))
    ∧ hwWitNachFlush = some (some (BitVec.ofNat 8 42)) := by
  obtain ⟨mW, hwW⟩ := kap_step_wort
  have hrW : TSOErreichbar (kapTso stapelWitM0) (kapTso mW) :=
    kap_union_wort_tso _ _ _ _ hwW
  obtain ⟨mS, hwS⟩ := kap_step_stapel
  have hrS : TSOErreichbar (kapTso stapelWitM0) (kapTso mS) :=
    kap_union_stapel_tso _ _ _ _ hwS
  obtain ⟨mD, hwD⟩ := kap_step_drain
  have hrD : TSOErreichbar (kapTso drainWitM0) (kapTso mD) :=
    kap_union_drain_tso _ _ _ _ hwD
  obtain ⟨mF, hwF⟩ := kap_step_fwd
  have hrF : TSOErreichbar (kapTso witFwdM0) (kapTso mF) :=
    kap_union_fwd_tso _ _ _ _ hwF
  have hstep : HwSchritt stapelWitM0 stapelWitM0
      (.leseBeob 0 stapelWitSlotAddr (BitVec.ofNat 8 0)) :=
    (kap_basis_embedded _ _ _).mpr kap_step_basis
  have hload := kapTso_basis_beob 0 stapelWitSlotAddr
    (BitVec.ofNat 8 0) hstep
  exact ⟨⟨mW, hwW, hrW⟩, ⟨mS, hwS, hrS⟩, ⟨mD, hwD, hrD⟩,
    ⟨mF, hwF, hrF⟩, kap_step_basis, hload,
    hwWit_weiterleitung, hwWit_fremd_alt,
    hwWit_spülung_aendert_speicher⟩

/- CUTS:
   Proved here, over the reused accepted vocabulary only (every
   definition lifted, never redefined):
   - projection `kapTso` of `HwMaschine` to the TSO-only machine
     (`tsoAnsicht`: shared memory plus per-core store buffers);
   - exact base classification `kap_basis_tso_klass`: register and
     fault steps are silent, loads observe with forwarding
     (`loadByte`), issues are single `issueByte` events, drains are
     single `flushKern` events with the buffer head named; the
     footprint (core, address, value, entry) is named in each leg;
   - multi-step reachability `TSOErreichbar` for the word, drain,
     forwarding and stack adapters (`kap_wort_tso`, `kap_drain_tso`,
     `kap_fwd_tso`, `kap_stapel_tso` via the `issueListe` induction
     `kapTso_issueListe_erreichbar`): word stores buffer eight bytes,
     drains flush one oldest entry, foreign issues issue one byte,
     observations are silent;
   - union lifts `kap_union_basis_tso`, `kap_union_wort_tso`,
     `kap_union_drain_tso`, `kap_union_fwd_tso`,
     `kap_union_stapel_tso` and the joint summary `kap_fuenf_tso`;
   - joint witness `kapTso_zeuge`: four exhibited union steps reach
     through the projection, the base observation reads zero through
     it, and the two-core non-degeneracy holds (owner forwards 42,
     foreign core reads stale 0, drain installs 42 into shared memory).
   NOT proved here, and not claimed (FINDINGs for follow-ups):
   - the remaining 16 union tags (lockRmw, isa, addr, muldiv,
     lockFetch, uc, port, fp, fehler, tor, vec, nested, int, system,
     bild, instanzen) are NOT classified here. In particular:
     lockRmw writes shared memory directly (`einbettenLock` takes the
     locked successor memory, not a flush) and needs the drained-own-
     buffer guard as a separate locked-RMW leg; the system plug
     installs memory directly (`sysSnapSchritt` ok-case); isa/addr
     need their own `concIssue` fold lemmas; uc/port take device
     paths; fp/fehler/tor/vec/nested/int/bild/instanzen need their
     control-state or register-path lemmas. No silent TSO bypass was
     found among them; each needs its producer file's equations.
   - no W/GX bridge (target-only reachability; `tso_last_lesbar` is
     cited, not re-proved); no whole-word atomicity beyond the
     guarded drains (`WortGruppe`/`FremdFrei` live in the family
     files); no source, checker, contract, entry, ABI, loader,
     budget or liveness claim; no hardware correspondence beyond
     self-consistency (silicon and timing assumptions live in the
     family files, not re-checked here).
-/

#print axioms kapTso
#print axioms kapTso_setKernDaten
#print axioms kapTso_setTso
#print axioms kapTso_setKernVonFp
#print axioms kap_basis_tso_klass
#print axioms kapTso_erreichbar_trans
#print axioms kapTso_schritt_erreichbar
#print axioms kapTso_issueListe_erreichbar
#print axioms kapTso_wortAusgabe_erreichbar
#print axioms kap_wort_tso
#print axioms kap_drain_tso
#print axioms kap_fwd_tso
#print axioms kap_stapelPush_erreichbar
#print axioms kap_stapelCall_erreichbar
#print axioms kap_stapel_tso
#print axioms kap_basis_reichbar
#print axioms kap_union_basis_tso
#print axioms kap_union_wort_tso
#print axioms kap_union_drain_tso
#print axioms kap_union_fwd_tso
#print axioms kap_union_stapel_tso
#print axioms kap_fuenf_tso
#print axioms kapTso_basis_beob
#print axioms kapTso_zeuge

end Gabbro.Grammatik.X86
