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
import Grammatik.X86.HwKapstein

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

/- CUTS:
   Skeleton only: projection and core-data silence.
   NOT proved yet: base classification, word/drain/fwd/stack reachability,
   locked RMW guard, joint witness, remaining-tag findings.
   No W/GX, no whole-word atomicity beyond guarded drains, no silicon claim.
-/

#print axioms kapTso
#print axioms kapTso_setKernDaten

end Gabbro.Grammatik.X86
