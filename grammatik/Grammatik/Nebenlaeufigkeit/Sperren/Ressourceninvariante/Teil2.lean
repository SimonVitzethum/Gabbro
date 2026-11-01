module

public import Grammatik.Kern.Semantik.Maschine
public import Grammatik.Nebenlaeufigkeit.Sperren.RessourcenBlatt.Teil3
public import Grammatik.Korpus.Referenz.ReferenzB
public import Grammatik.Nebenlaeufigkeit.Sperren.Ressourceninvariante.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}

/-- The witness invariant is local: it reads only `konto` slots. -/
theorem refInv81_lokal (s s' : Speicher refD)
    (h : ∀ k f, s.slots () k f = s'.slots () k f) :
    refInv81 s ↔ refInv81 s' := by
  constructor
  ·
    intro hs
    show s'.slots () 0 () = s'.slots () 1 ()
    rw [← h 0 (), ← h 1 (), hs]
  ·
    intro hs
    show s.slots () 0 () = s.slots () 1 ()
    rw [h 0 (), h 1 (), hs]

/-- The witness invariant holds at the start: both slots read `0`. -/
theorem refInv81_start : refInv81 refSp0 := by rfl

/-- The witness release premise: on `refB_prog` no step can move the lock
    from held to free. `take` only gains it (against its own `hself`);
    `leaf` preserves held locks (`blatt_brav`); `rel` atoms never occur
    (`refB_prog_kein_rel`). The reachability hypothesis is logically
    redundant here -- every held-to-free transition is already impossible
    per step -- and is recorded as such (merged precedent: `hNoAx0` in
    `EigenZustandD.lean` leaves most of its joint hypotheses unused). -/
theorem refInv81_release (M : GenMaschine refD) (pc : PCStand) (f : Faden)
    (M' : GenMaschine refD) (pc' : PCStand)
    (hreach : PCReach refP refO 0 refB_prog (GenStart refSp0) M pc)
    (hs : PCSchritt refP refO 0 refB_prog M pc f M' pc')
    (hlt1 : () ∈ offen (M.spuren f)) (hlt2 : () ∉ offen (M'.spuren f)) :
    refInv81 M'.speicher := by
  cases hs with
  | leaf V l Γ Λ Λ' s ρ hleaf hΛ σ' _ hstep _ _ _ _ _ _ _ _ =>
      have hbrav := blatt_brav refO 0 refO_gut M f V l Γ Λ Λ' s ρ hΛ σ' hstep
      have hopenf : offen σ'.spur = offen (M.spuren f) := by
        have e1 : σ'.haelt = offen σ'.spur := rfl
        have e2 : (M.weltVon f).haelt = offen (M.spuren f) := rfl
        rw [← e1, ← e2]
        exact hbrav.1
      have hcon : () ∈ offen σ'.spur := hopenf ▸ hlt1
      have hff : () ∉ offen σ'.spur := by
        have h := hlt2
        simp only [genUpdate_self] at h
        exact h
      exact absurd hcon hff
  | take L' hself _ _ _ =>
      have eL' : L' = () := by cases L'; rfl
      rw [eL'] at hself
      exact absurd hlt1 hself
  | rel L' _ hpc =>
      exact False.elim (refB_prog_kein_rel f (pc f) L' hpc)

/-- A memory where the witness invariant fails: slot `0` reads `100`,
    slot `1` reads `0`. The invariant is not trivially true. -/
def badSp81 : Speicher refD :=
  ⟨fun _ k _ => if k = 0 then (⟨100, by decide, by decide⟩ : Wert refD (.int 0 100))
      else (⟨0, by decide, by decide⟩ : Wert refD (.int 0 100)),
   fun g => nomatch g⟩

/-- The witness invariant is not trivially true: it fails at `badSp81`. -/
theorem badSp81_neg : ¬ refInv81 badSp81 := by
  intro h
  have h0 : badSp81.slots () 0 () =
      (⟨100, by decide, by decide⟩ : Wert refD (refD.typ () ())) := rfl
  have h1 : badSp81.slots () 1 () =
      (⟨0, by decide, by decide⟩ : Wert refD (refD.typ () ())) := rfl
  unfold refInv81 at h
  rw [h0, h1] at h
  have hn := congrArg Zahl.n h
  simp only [Int.reduceEq] at hn

/-! ## 5. Inhabitation (rule 13): all premises hold jointly -/

/-- **Inhabitation.** All premises of `csl_ressourceninvariante` hold jointly
    on the reference fixture (`refP`/`refO`/`refB_prog`/`refSp0`, table
    `konto`, its lock, invariant "the two slots agree"), the theorem's own
    conclusion is exhibited at those values, the invariant is not trivially
    true (`badSp81`), some function writes the table (`refEin`), and a
    reached run moves memory (`refB_pc_erreicht`/`refB_pc_schreibt`:
    `take` then the writing leaf, slot `0 -> 100`). -/
theorem csl_ressourceninvariante_zeuge :
    GutO refO
    ∧ Sum.inl () ∈ refD.braucht ()
    ∧ (∀ s s' : Speicher refD,
        (∀ k f, s.slots () k f = s'.slots () k f) → (refInv81 s ↔ refInv81 s'))
    ∧ refInv81 refSp0
    ∧ (∀ M pc f M' pc', PCReach refP refO 0 refB_prog (GenStart refSp0) M pc →
        PCSchritt refP refO 0 refB_prog M pc f M' pc' →
        () ∈ offen (M.spuren f) → () ∉ offen (M'.spuren f) → refInv81 M'.speicher)
    ∧ (∀ M pc, PCReach refP refO 0 refB_prog (GenStart refSp0) M pc →
        (∀ g, () ∉ offen (M.spuren g)) → refInv81 M.speicher)
    ∧ (∃ σ : Speicher refD, ¬ refInv81 σ)
    ∧ (vertragVon refD refEin).schreibt () = true
    ∧ ∃ (M : GenMaschine refD) (pc : PCStand),
        PCReach refP refO 0 refB_prog (GenStart refSp0) M pc ∧
        M.speicher.slots () 0 () ≠ refSp0.slots () 0 () := by
  exact ⟨refO_gut, refInv81_guard, refInv81_lokal, refInv81_start,
    refInv81_release,
    csl_ressourceninvariante refP refO 0 refO_gut refB_prog refSp0
      () () refInv81 refInv81_guard refInv81_lokal refInv81_start refInv81_release,
    ⟨badSp81, badSp81_neg⟩, refEin_schreibt (),
    refPC2, refB_pc2, refB_pc_erreicht, refB_pc_schreibt⟩

/-! ## CUTS
  - Green (standard axioms only): `refInv81`, `blatt_erhaelt_slots` (leaf
    extension including `axiomCall`), `csl_ressourceninvariante` (the main
    theorem), and the rule-13 witness `csl_ressourceninvariante_zeuge` with
    its helpers (`refB_prog_kein_rel`, `refInv81_guard`, `refInv81_lokal`,
    `refInv81_start`, `refInv81_release`, `badSp81`, `badSp81_neg`).
  - Not proved (documented findings, no `sorry`): the `hreach` hypothesis
    of `refInv81_release` is logically redundant -- every held-to-free
    transition is already impossible per step on `refB_prog` (the linter
    warning says so openly; merged precedent `hNoAx0` in
    `EigenZustandD.lean` is the same shape).
-/

#print axioms Gabbro.Grammatik.refInv81
#print axioms Gabbro.Grammatik.blatt_erhaelt_slots
#print axioms Gabbro.Grammatik.csl_ressourceninvariante
#print axioms Gabbro.Grammatik.csl_ressourceninvariante_zeuge

end Gabbro.Grammatik
