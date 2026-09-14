/-
  Gabbro/Grammatik/FortschrittZeuge.lean

  **The witness for `fortschrittG_aus`** (SATZKARTE §19.2) on the
  two-writer fixture of `MehrfadenZeuge.lean` (`mP`: thread 0 runs
  `hauptA`, thread 1 `hauptB`, both take the one lock around a call of
  `setze`; every other thread runs `ruhe`).

  On a reached machine (the one of `keine_verklemmungG_zeuge`: thread 0
  has taken the lock and stands at the call of `setze` inside it, thread 1
  stands at its `locks`), the theorem classifies every thread:

  * thread 1 WAITS for the lock thread 0 holds (`WartetG`);
  * thread 0 is not finished, does not wait, and stands at no named
    hardware stop -- so it can step, BY THE THEOREM;
  * every idle thread is finished.
-/
import Grammatik.Fortschritt
import Grammatik.MehrfadenLauf

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. Where a named stop can stand -/

/-- The block forms whose first layer can answer hardware. -/
def Block.kannHalten {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Block D V l Γ Λ Λ' → Bool
  | .cons s _ => s.istBlatt
  | .bindAxiom .. => true
  | .regLies .. => true
  | .regLiesElse .. => true
  | .awaits .. => true
  | .gleit .. => true
  | .gleitLit .. => true
  | .gleitVon .. => true
  | _ => false

/-- The residues at which a named hardware stop can stand. -/
def GRest.kannHalten {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    GRest D V l Γ Λ → Bool
  | .ewig _ n _ _ _ => n == 0
  | .ende e =>
      match e with
      | .cons s _ => s.istBlatt
      | _ => false
  | .dann b _ => b.kannHalten
  | _ => false

/-- A named hardware stop stands only where `kannHalten` says. -/
theorem restHardware_kann {O : Orakel D} {passes : Nat} {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} {σ : World D} {ρ : Env D Γ} (r : GRest D V l Γ Λ)
    (h : Zielsatz.RestHardware O passes σ ρ r) : r.kannHalten = true := by
  cases r with
  | ewig a n inv body k =>
      cases n with
      | zero => rfl
      | succ n => exact absurd h (by simp [Zielsatz.RestHardware])
  | ende e =>
      cases e with
      | cons s rest => exact h.1
      | _ => exact absurd h (by simp [Zielsatz.RestHardware])
  | dann b k =>
      cases b with
      | cons s rest => exact h.1
      | bindAxiom => rfl
      | regLies => rfl
      | regLiesElse => rfl
      | awaits => rfl
      | gleit => rfl
      | gleitLit => rfl
      | gleitVon => rfl
      | _ => exact absurd h (by simp [Zielsatz.RestHardware, Zielsatz.KopfHardware])
  | _ => exact absurd h (by simp [Zielsatz.RestHardware])

/-- A thread whose head residue cannot hold a named stop stands at none. -/
theorem nicht_haltBenannt {O : Orakel D} {passes : Nat} {M : RufMaschineG D} {t : Faden}
    (h : (M.faeden t).kopf.rest.2.2.2.2.kannHalten = false) :
    ¬ Zielsatz.HaltBenannt O passes M t := by
  rintro ⟨l, Γ, Λ, ρ, r, hr, hh⟩
  have e := congrArg (fun x => x.2.2.2.2.kannHalten) hr
  simp only at e
  rw [h, restHardware_kann r hh] at e
  exact Bool.false_ne_true e

/-! ## 2. The reached machine -/

/-- **`fortschritt_zeuge`**: on a machine of the two-writer program reached
    in six steps, `fortschrittG_aus` holds (all its premises are the
    fixture's) and classifies every thread: thread 1 waits for the lock
    thread 0 holds; thread 0 is neither finished nor waiting nor at a
    named stop, so it can step BY THE THEOREM; every idle thread is
    finished. -/
theorem fortschritt_zeuge : ∃ M : RufMaschineG mD,
    RufErreichbarG mP mO 0 (RufStartG mP mSp mInit) M ∧
    Zielsatz.FortschrittG mP mO 0 M ∧
    (¬ FertigG M 0 ∧ ¬ WartetG M 0 ∧ ¬ Zielsatz.HaltBenannt mO 0 M 0 ∧
      ∃ M', RufSchrittG mP mO 0 M 0 M') ∧
    (WartetG M 1 ∧ ¬ FertigG M 1) ∧
    ∀ t : Nat, 2 ≤ t → FertigG M t := by
  obtain ⟨M, σ0, σ1, log0, log1, hr, hz0, hoff0, hz1, hoff1, hidle⟩ := mVorlauf
  have hfrei0 : RufFreiG M 0 () := mFrei fun g hg => by
    by_cases hg1 : g = 1
    · subst hg1; rw [hz1.spur]; exact hoff1
    · rw [hidle g hg hg1]; exact mStart_offen g
  obtain ⟨Ms, ss, hZs⟩ := w_locks (P := mP) (O := mO) (passes := 0) hz0.1 ()
    _ _ _ _ _ rfl (mhg0 hoff0) hfrei0
  have hrs : RufErreichbarG mP mO 0 (RufStartG mP mSp mInit) Ms := .schritt _ _ _ hr ss
  have hs1 : Ms.faeden 1 = M.faeden 1 := rufSchrittG_fremd ss 1 (by decide)
  have hoff0' : offen (M.faeden 0).spur = [] := by rw [hz0.spur]; exact hoff0
  have hoffs : offen (Ms.faeden 0).spur = [()] := by
    rw [hZs.spur]
    exact congrArg (List.cons ()) hoff0'
  -- the theorem, from the fixture's premises
  have hF : Zielsatz.FortschrittG mP mO 0 Ms :=
    fortschrittG_aus mO_gut mP_stufen mSp mInit (startSpur_nodup_leer mInit mInit_leer) hrs
      (mP_zertifiziert 0 Ms hrs).1.1.2.2.1
  -- thread 1 waits
  have hW : WartetG Ms 1 :=
    ⟨⟨(), anSperre_von (hs1.trans hz1.1)⟩, fun L _ => ⟨0, by decide, by
      cases L; rw [hoffs]; exact List.mem_cons_self⟩⟩
  have hF1 : ¬ FertigG Ms 1 := fun h => by
    have := h.2
    rw [hs1, hz1.1] at this
    exact Bool.false_ne_true this
  -- thread 0: not finished, not waiting, not at a named stop
  have hF0 : ¬ FertigG Ms 0 := fun h => by
    have := h.2
    rw [hZs.1] at this
    exact Bool.false_ne_true this
  have hW0 : ¬ WartetG Ms 0 := fun h => by
    obtain ⟨L, l, Γ, Λ, Λ'', ρ, hr', body, rest, k, hk⟩ := h.1
    have := congrArg (fun x => x.2.2.2.2.istLocks) hk
    simp only [GRest.istLocks] at this
    rw [hZs.1] at this
    exact Bool.false_ne_true this
  have hH0 : ¬ Zielsatz.HaltBenannt mO 0 Ms 0 := nicht_haltBenannt (by rw [hZs.1]; rfl)
  -- so the theorem gives thread 0 a step
  have hS0 : ∃ M', RufSchrittG mP mO 0 Ms 0 M' := by
    rcases hF 0 with h | h | h | h
    · exact absurd h hF0
    · exact absurd h hW0
    · exact absurd h hH0
    · exact h
  -- the idle threads are finished
  have hRuhe : ∀ t : Nat, 2 ≤ t → FertigG Ms t := by
    intro t ht
    have h0 : t ≠ 0 := fun h => by subst h; exact absurd ht (by decide)
    have h1 : t ≠ 1 := fun h => by subst h; exact absurd ht (by decide)
    have e : Ms.faeden t = (RufStartG mP mSp mInit).faeden t := by
      rw [rufSchrittG_fremd ss t h0]
      exact hidle t h0 h1
    have hi : mInit t = ⟨mRuhe, .nil⟩ := by
      unfold mInit
      rw [if_neg h0, if_neg h1]
    refine ⟨by rw [e, start_faden], ?_⟩
    rw [e, start_faden, hi]
    rfl
  exact ⟨Ms, hrs, hF, ⟨hF0, hW0, hH0, hS0⟩, ⟨hW, hF1⟩, hRuhe⟩

#print axioms Gabbro.Grammatik.restHardware_kann
#print axioms Gabbro.Grammatik.nicht_haltBenannt
#print axioms Gabbro.Grammatik.fortschritt_zeuge

end Gabbro.Grammatik
