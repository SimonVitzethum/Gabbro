module

public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.InterferenzAllgemein
public import Grammatik.Kern.Semantik.Maschine
public import Grammatik.Korpus.Referenz.ReferenzB
public import Grammatik.Nebenlaeufigkeit.Allgemein.DisziplinBedarf.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}

/-- Every writing step holds the guard: the only written carrier is
    `konto`, whose watch list forces the lock. -/
theorem bedWatch : ∀ (c : bedD.Tab ⊕ bedD.Glob) (L : bedD.Lock) (k : Nat)
    (g : Faden) (vor nach : World bedD),
    Bewacht (D := bedD) c L → g ∈ bedJ.faeden → bedJ.schrittFaden[k]? = some g →
      bedJ.welten[k]? = some vor → bedJ.welten[k + 1]? = some nach →
        TraegerSchreibt (bedJ.code g) c = true → L ∈ bedD.haelt (bedJ.code g) := by
  intro c L k g vor nach hB hg hkg hkv hkn hw
  rw [bedJ_faeden] at hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  subst hg
  rw [bedJ_welten] at hkn
  have hk0 : k = 0 := by
    have hlen : k + 1 < [bedW0, bedW1].length := lt_of_belegt _ _ _ hkn
    simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd] at hlen
    omega
  subst hk0
  cases c with
  | inl t =>
    cases t with
    | true =>
      have hL : L = () := by
        simp only [Bewacht, bedBraucht_konto] at hB
        have h2 : Sum.inl L = Sum.inl () := List.mem_singleton.mp hB
        injection h2 with hL'
      subst hL
      show () ∈ ([()] : List bedD.Lock)
      exact List.mem_singleton.mpr rfl
    | false => exact absurd hw (by decide)
  | inr x => exact nomatch x

/-- The old guard-existence premise is FALSE here: `config` has no
    guard. This is the separate lemma the narrowed premise improves on. -/
theorem bedGuardEx_falsch :
    ¬ ∀ c : bedD.Tab ⊕ bedD.Glob,
      ∃ L : bedD.Lock, Bewacht (D := bedD) c L := by
  intro h
  obtain ⟨L, hL⟩ := h (.inl false)
  simp only [Bewacht, bedBraucht_config] at hL
  simp only [List.not_mem_nil] at hL

/-- **Inhabitation (rule 13).** All premises of
    `invariantenKontext_aus_disziplin_bedarf` hold jointly on the
    two-table witness (`bedD`/`bedNb`/`bedJ`/`bedI`): `konto` is written
    and guarded, `config` is only read and unguarded. The old
    `hGuardEx` is false there (`bedGuardEx_falsch`), so the narrowed
    premise is strictly weaker. Non-degeneracy: the writer writes
    `konto` (`bedSchreibt_konto`), the chain step changes memory
    (`bedMemWechsel`), and the reference fixture contributes a reached
    run that moves memory (`refB_pc_erreicht`/`refB_pc_schreibt`). -/
theorem invariantenKontext_aus_disziplin_bedarf_zeuge :
    (∀ c, HaengtAb (bedWc c) (bedGc c) (bedI.inv c))
    ∧ (∀ (c : bedD.Tab ⊕ bedD.Glob) (t : bedD.Tab),
        bedWc c t = true → c = .inl t)
    ∧ (∀ (c : bedD.Tab ⊕ bedD.Glob) (x : bedD.Glob),
        bedGc c x = true → c = .inr x)
    ∧ (∀ c : bedD.Tab ⊕ bedD.Glob,
        (∃ g, g ∈ bedJ.faeden ∧ TraegerSchreibt (bedJ.code g) c = true) →
          ∃ L : bedD.Lock, Bewacht (D := bedD) c L)
    ∧ (∀ (c : bedD.Tab ⊕ bedD.Glob) (σ₀ : World bedD),
        bedJ.welten[0]? = some σ₀ → bedI.inv c σ₀)
    ∧ (∀ (c : bedD.Tab ⊕ bedD.Glob) (L : bedD.Lock) (k : Nat) (g : Faden)
        (vor nach : World bedD),
        Bewacht (D := bedD) c L → g ∈ bedJ.faeden →
          bedJ.schrittFaden[k]? = some g → bedJ.welten[k]? = some vor →
            bedJ.welten[k + 1]? = some nach →
              TraegerSchreibt (bedJ.code g) c = true →
                L ∈ bedD.haelt (bedJ.code g) → bedI.inv c nach)
    ∧ (∀ (c : bedD.Tab ⊕ bedD.Glob) (L : bedD.Lock) (k : Nat) (g : Faden)
        (vor nach : World bedD),
        Bewacht (D := bedD) c L → g ∈ bedJ.faeden →
          bedJ.schrittFaden[k]? = some g → bedJ.welten[k]? = some vor →
            bedJ.welten[k + 1]? = some nach →
              TraegerSchreibt (bedJ.code g) c = true →
                L ∈ bedD.haelt (bedJ.code g))
    ∧ InvariantenKontext bedNb bedJ bedI
    ∧ (¬ ∀ c : bedD.Tab ⊕ bedD.Glob,
        ∃ L : bedD.Lock, Bewacht (D := bedD) c L)
    ∧ (∃ f : bedD.Fn, TraegerSchreibt f (.inl true) = true)
    ∧ (∃ k vor nach, bedJ.welten[k]? = some vor ∧
        bedJ.welten[k + 1]? = some nach ∧
        vor.slots true 0 () ≠ nach.slots true 0 ())
    ∧ ∃ (M : GenMaschine refD) (pc : PCStand),
        PCReach refP refO 0 refB_prog (GenStart refSp0) M pc ∧
        M.speicher.slots () 0 () ≠ refSp0.slots () 0 () := by
  refine ⟨bedAb, bedFrameT, bedFrameG, bedGuardBedarf, bedEntry, bedReturn,
    bedWatch, ?_, bedGuardEx_falsch, ⟨true, bedSchreibt_konto⟩,
    ⟨0, bedW0, bedW1, by simp only [bedJ_welten, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.zero_lt_succ,
  getElem?_pos, List.getElem_cons_zero], by simp only [bedJ_welten, Nat.zero_add, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.lt_add_one,
  getElem?_pos, List.getElem_cons_succ, List.getElem_cons_zero],
      Ne.symm bedMemWechsel⟩,
    refPC2, refB_pc2, refB_pc_erreicht, refB_pc_schreibt⟩
  exact invariantenKontext_aus_disziplin_bedarf bedNb bedJ bedI bedWc bedGc
    bedAb bedFrameT bedFrameG bedGuardBedarf bedEntry bedReturn bedWatch

/-! ## CUTS:
  - Proved: `traegerStill_ohneSchreiber` (helper), the target
    `invariantenKontext_aus_disziplin_bedarf`, and its rule-13 witness
    `invariantenKontext_aus_disziplin_bedarf_zeuge` with the two-table
    fixture (`bedD`, `bedJ`, `bedI`, footprints, all premise proofs) and
    the separate `bedGuardEx_falsch` lemma.
  - The witness invariant is trivially true, so `bedEntry`/`bedReturn`
    use only the world-identification hypotheses; the guard hypotheses
    of `bedReturn` are unused there (same shape as the merged precedent
    `refInv81_release`, whose reachability hypothesis is documented
    redundant). A minimal one-step chain cannot exercise restoration.
  - The witness is NOT on the reference fixture: `refD` has a single
    carrier, so the old `hGuardEx` cannot fail there. The task's demand
    (one written guarded carrier plus one read-only unguarded carrier)
    forces a two-carrier declaration; see the report.
-/

#print axioms Gabbro.Grammatik.traegerStill_ohneSchreiber
#print axioms Gabbro.Grammatik.invariantenKontext_aus_disziplin_bedarf
#print axioms Gabbro.Grammatik.invariantenKontext_aus_disziplin_bedarf_zeuge
#print axioms Gabbro.Grammatik.bedGuardEx_falsch

end Gabbro.Grammatik
