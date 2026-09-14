/-
  File:      Grammatik/Nichtinterferenz/ZeugeMehrfaden.lean
  Subject:   THE REFERENCE FIXTURE for the premises of `nichtinterferenz`:
             the two-thread witness `mD`/`mP` of `MehrfadenZeuge.lean`
             (a lock, a shared account, two private tables, two active
             threads), under a WRITE-UP labelling.

  `Korpus.lean` shows `mP` refused under every label of `konto` in the
  three-point tenant policy: both tenants write `konto`, and no label lies
  above both. With a TOP domain `T` above `A` and `B` (a diamond: `K` below
  everything, `T` above everything), `konto` labelled `T` is a WRITE-ONLY
  SINK for the tenants: both may write it, neither may read it, only `T`
  (an auditor) sees it. Under that policy `mP` passes `flussB`
  (`n124_fluss`), and every premise of `nichtinterferenz` holds jointly on
  the fixture with a reached two-step run (`n124_zeuge`).

  The fixture also shows what the theorem does NOT see: `mP`'s lock `L` is
  taken by both tenants. Whether thread 1 can take `L` depends on thread 0
  -- an enabledness channel (`dokumente/NICHTINTERFERENZ.md` §3, §7.4). The
  theorem is sound for it because it compares only runs that follow the
  schedule; the checker proposal `I005` would refuse the shared lock.
-/
import Grammatik.Nichtinterferenz.Fluss
import Grammatik.MehrfadenLauf

namespace Gabbro.Grammatik

namespace NIZeuge

/-- Four domains: `K` below everything, `T` above everything. -/
inductive Dom4 where
  | K
  | A
  | B
  | T
  deriving DecidableEq

def darf4 : Dom4 → Dom4 → Bool
  | .K, _ => true
  | _, .T => true
  | .A, .A => true
  | .B, .B => true
  | _, _ => false

def π4 : Politik Dom4 where
  darf := darf4
  refl := fun d => by cases d <;> rfl
  trans := fun a b c h1 h2 => by
    cases a <;> cases b <;> cases c <;> simp_all [darf4]

/-- The write-up labelling: `konto` is a sink of the top domain. -/
def L124w : FlussEtiketten mD Dom4 where
  lab
    | .inl .konto => .T
    | .inl .privA => .A
    | .inl .privB => .B
  labAx := fun a => nomatch a
  wurzel
    | .hauptA => some .A
    | .hauptB => some .B
    | .ruhe => some .K
    | _ => none

def cs124 : List (mD.Tab ⊕ mD.Glob) := [.inl .konto, .inl .privA, .inl .privB]

theorem cs124_voll : ∀ c : mD.Tab ⊕ mD.Glob, c ∈ cs124 := by
  intro c
  cases c with
  | inl t => cases t <;>
      (unfold cs124; repeat (first | exact List.mem_cons_self | apply List.mem_cons_of_mem))
  | inr g => exact nomatch g

/-- **The two-thread fixture passes the flow check under the write-up
    labelling.** -/
theorem n124_fluss : flussB π4 mP mFs cs124 L124w = true := by decide

def fdom124 : Faden → Dom4 := fun t => if t = 0 then .A else if t = 1 then .B else .K

theorem n124_wurzel : ∀ t, L124w.wurzel (mInit t).1 = some (fdom124 t) := by
  intro t
  unfold mInit fdom124
  by_cases h0 : t = 0
  · simp only [h0, if_true]; rfl
  · by_cases h1 : t = 1
    · simp only [h1, if_true, show (1 : Nat) ≠ 0 from by decide, if_false]; rfl
    · simp only [h0, h1, if_false]; rfl

/-- A reached two-step run of the fixture: thread 0 writes `privA[0]`,
    thread 1 writes `privB[0]`. -/
theorem n124_lauf : ∃ ms : Nat → RufMaschineG mD,
    LaufG mP mO 0 (RufStartG mP mSp mInit) ms (fun k => k) 2 ∧
    (ms 2).speicher.slots MTab.privB 0 () ≠ mSp.slots MTab.privB 0 () := by
  obtain ⟨M1, s1, hZ1⟩ := w_blatt (P := mP) (O := mO) (passes := 0) mStart0
    _ _ _ rfl rfl (mHeld0 _) _ _ (execStmt_assignSlot _ _ _ _ _ _ _ _ _ _ _)
    ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _))
  have h1 : M1.faeden 1 = (RufStartG mP mSp mInit).faeden 1 :=
    rufSchrittG_fremd s1 1 (by decide)
  obtain ⟨M2, s2, hZ2⟩ := w_blatt (P := mP) (O := mO) (passes := 0) (h1.trans mStart1)
    _ _ _ rfl rfl (mHeld0 _) _ _ (execStmt_assignSlot _ _ _ _ _ _ _ _ _ _ _)
    ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _))
  refine ⟨fun k => match k with
    | 0 => RufStartG mP mSp mInit
    | 1 => M1
    | _ => M2, ⟨rfl, fun k hk => ?_⟩, ?_⟩
  · match k, hk with
    | 0, _ => exact s1
    | 1, _ => exact s2
  · show M2.speicher.slots MTab.privB 0 () ≠ mSp.slots MTab.privB 0 ()
    rw [hZ2.2]
    intro h
    have h5 : (5 : Int) = 0 := congrArg Zahl.n h
    exact absurd h5 (by decide)

/-- **`nichtinterferenz` on the reference fixture (`n124_zeuge`).** Every
    premise holds jointly on the two-thread fixture with a lock: the flow
    check, the labelled roots, the oracle conditions, and a reached run of
    two steps that moves memory; the theorem then gives, for the observer
    `B` and that run taken twice, equal observations. -/
theorem n124_zeuge :
    flussB π4 mP mFs cs124 L124w = true ∧
    ∃ ms : Nat → RufMaschineG mD,
      LaufG mP mO 0 (RufStartG mP mSp mInit) ms (fun k => k) 2 ∧
      (ms 2).speicher.slots MTab.privB 0 () ≠ mSp.slots MTab.privB 0 () ∧
      ∀ k, k ≤ 2 → beob π4 (etiketten L124w fdom124) Dom4.B (ms k) =
        beob π4 (etiketten L124w fdom124) Dom4.B (ms k) := by
  obtain ⟨ms, hl, hmove⟩ := n124_lauf
  exact ⟨n124_fluss, ms, hl, hmove,
    nichtinterferenz π4 mP mO 0 mInit L124w fdom124 mFs_voll cs124_voll n124_fluss n124_wurzel
      Dom4.B mO_gut mO_lokal (fun a => nomatch a) mSp mSp (SpeicherGleich.refl _ _) ms ms
      (fun k => k) 2 hl hl⟩

#print axioms Gabbro.Grammatik.NIZeuge.n124_zeuge

end NIZeuge

end Gabbro.Grammatik
