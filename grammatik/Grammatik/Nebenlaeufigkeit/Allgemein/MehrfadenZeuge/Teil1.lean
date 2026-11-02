/-
  File:      Grammatik/MehrfadenZeuge.lean
public import Grammatik.Nebenlaeufigkeit.Allgemein.MehrfadenZeuge.Teil1Basis
  Subject:   THE WITNESS for the three concurrency repairs of 2026-09-14
             (THEOREM-MAP §16): two ACTIVE threads, each writing its OWN
             private table unguarded, both updating one shared table under a
             lock with a non-trivial lock invariant.

  Declaration `mD`: tables `konto` (shared, guarded by the lock `()`),
  `privA` and `privB` (UNGUARDED, not shared), two slots each, values
  `0 .. 100`; one table invariant `privA[0] == privA[1]`.

  * `setze(x)` (holds the lock by signature): requires
    `konto[0] == konto[1]`, ensures `konto[0] == konto[1] && konto[0] == x`,
    writes `x` into both `konto` slots.
  * `hauptA()` (thread 0): `privA[0] = 7; privA[1] = 7; locks { setze(30) };
    pruefeA(); return`, ensures `privA[0] == 7`, OWES the invariant (it
    writes `privA`).
  * `hauptB()` (thread 1): `privB[0] = 5; locks { setze(70) }; return`.
  * `pruefeA()`: REQUIRES `privA[0] == 7`, returns.
  * `ruhe()`: every other thread, returns.

  Lock invariant `konto[0] == konto[1]`. The per-thread call graphs:
  `{hauptA, setze, pruefeA}`, `{hauptB, setze}`, `{ruhe}`.

  Both earlier footprint checks REFUSE the program (`mP_fussS_falsch`:
  `hauptA`'s footprint holds `privA`, unguarded and written); the new one
  passes (`mP_fussMehr`). Every premise of the new flagship
  `ziel_ort_mehrfaden_ende` holds (`mP_zertifiziert`), and of the deadlock
  theorem (`mP_verklemmungsfrei`). The runs are in `MehrfadenLauf.lean`.
-/
module

public import Grammatik.Nebenlaeufigkeit.Allgemein.Verklemmung
public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtSperreZeuge

@[expose] public section



namespace Gabbro.Grammatik
/-- `setze(x)`: `konto[0] = x; konto[1] = x; return`. -/
def mRumpfSetze : Endblock mD (vertragVon mD mSetze) false [.int 0 100] mL :=
  .cons (.assignSlot MTab.konto () mI0 (.var .here) rfl mDarfK)
    (.cons (.assignSlot MTab.konto () mI1 (.var .here) rfl mDarfK) (.ret .empty (by rfl)))

/-- The call `setze(30)` inside `hauptA`'s lock. -/
def mRufA : Stmt mD (vertragVon mD mHauptA) false [] mL mL :=
  .call mSetze (.cons m30 .nil) mHpSetzeA rfl

/-- The call `setze(70)` inside `hauptB`'s lock. -/
def mRufB : Stmt mD (vertragVon mD mHauptB) false [] mL mL :=
  .call mSetze (.cons m70 .nil) mHpSetzeB rfl

/-- `hauptA`'s `locks { setze(30) }`. -/
def mLocksA : Stmt mD (vertragVon mD mHauptA) false [] [] [] :=
  .locks () (fun _ h => nomatch h) (.cons mRufA .nil)

/-- `hauptB`'s `locks { setze(70) }`. -/
def mLocksB : Stmt mD (vertragVon mD mHauptB) false [] [] [] :=
  .locks () (fun _ h => nomatch h) (.cons mRufB .nil)

/-- `pruefeA(); return` -- the tail of `hauptA`. -/
def mRestA : Endblock mD (vertragVon mD mHauptA) false [] [] :=
  .cons (.call mPruefeA .nil mHpPruefe rfl) (.ret .empty List.Perm.nil)

/-- `hauptA`: `privA[0] = 7; privA[1] = 7; locks { setze(30) }; pruefeA(); return`. -/
def mRumpfA : Endblock mD (vertragVon mD mHauptA) false [] [] :=
  .cons (.assignSlot MTab.privA () mI0 m7 rfl (mDarfA _))
    (.cons (.assignSlot MTab.privA () mI1 m7 rfl (mDarfA _))
      (.cons mLocksA mRestA))

/-- `hauptB`: `privB[0] = 5; locks { setze(70) }; return`. -/
def mRumpfB : Endblock mD (vertragVon mD mHauptB) false [] [] :=
  .cons (.assignSlot MTab.privB () mI0 m5 rfl (mDarfB _))
    (.cons mLocksB (.ret .empty List.Perm.nil))

/-- The program. -/
def mP : Programm mD where
  invariante := fun _ => mAGleich
  requires
    | .setze => mGleich
    | .pruefeA => mA7
    | _ => .tru
  ensures
    | .setze => .and mGleich (.eq (.slot MTab.konto () mI0 mDarfK) (.var .here))
    | .hauptA => mA7
    | _ => .tru
  rumpf
    | .setze => mRumpfSetze
    | .hauptA => mRumpfA
    | .hauptB => mRumpfB
    | .pruefeA => .ret .empty List.Perm.nil
    | .ruhe => .ret .empty List.Perm.nil

def mFs : List mD.Fn := [mSetze, mHauptA, mHauptB, mPruefeA, mRuhe]

theorem mFs_voll : ∀ g : mD.Fn, g ∈ mFs := by
  intro g
  cases g
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self)))

/-- **The lock invariant `konto[0] == konto[1]`**, protecting `konto`. -/
def mSI : SperrInv mD :=
  ⟨fun _ => [.inl MTab.konto], fun _ s => decide ((s.slots MTab.konto 0 ()).n = (s.slots MTab.konto 1 ()).n)⟩

theorem mSI_ok : SperrInvOk mSI := by
  refine ⟨fun L c hc => ?_, fun L s s' h => ?_⟩
  · cases L
    rw [List.mem_singleton.mp hc]
    exact List.mem_singleton.mpr rfl
  · have e : s.slots MTab.konto = s'.slots MTab.konto := h (.inl MTab.konto) List.mem_cons_self
    show decide ((s.slots MTab.konto 0 ()).n = (s.slots MTab.konto 1 ()).n) =
      decide ((s'.slots MTab.konto 0 ()).n = (s'.slots MTab.konto 1 ()).n)
    rw [e]

/-! ## 3. The call graphs and the footprint checks -/

def mKA : mD.Fn → Bool
  | .setze => true
  | .hauptA => true
  | .pruefeA => true
  | _ => false

def mKB : mD.Fn → Bool
  | .setze => true
  | .hauptB => true
  | _ => false

def mKR : mD.Fn → Bool
  | .ruhe => true
  | _ => false

/-- **The call graph of every thread**: thread 0 runs `hauptA` and what it
    calls, thread 1 `hauptB` and what it calls, every other `ruhe`. -/
def mK (t : Faden) : mD.Fn → Bool := if t = 0 then mKA else if t = 1 then mKB else mKR

/-- The call graphs are the computed reachable sets. -/
theorem mKA_reach (f : mD.Fn) : mKA f = reachB mP mFs mHauptA f := by cases f <;> decide
theorem mKB_reach (f : mD.Fn) : mKB f = reachB mP mFs mHauptB f := by cases f <;> decide

theorem mAbg : ∀ t, AbgK mP mFs (mK t) := by
  intro t
  unfold mK
  by_cases h0 : t = 0
  · rw [if_pos h0]; exact abgB_ok mFs_voll (by decide)
  · rw [if_neg h0]
    by_cases h1 : t = 1
    · rw [if_pos h1]; exact abgB_ok mFs_voll (by decide)
    · rw [if_neg h1]; exact abgB_ok mFs_voll (by decide)

/-- Thread 0 runs `hauptA`, thread 1 `hauptB`, every other thread `ruhe`. -/
def mInit : Faden → Σ f : mD.Fn, Env mD (mD.params f) :=
  fun t => if t = 0 then ⟨mHauptA, .nil⟩ else if t = 1 then ⟨mHauptB, .nil⟩ else ⟨mRuhe, .nil⟩

theorem mWurzel : ∀ t, mK t (mInit t).1 = true := by
  intro t
  unfold mK mInit
  by_cases h0 : t = 0
  · rw [if_pos h0, if_pos h0]; rfl
  · rw [if_neg h0, if_neg h0]
    by_cases h1 : t = 1
    · rw [if_pos h1, if_pos h1]; rfl
    · rw [if_neg h1, if_neg h1]; rfl

theorem mStumm : ∀ t, 2 ≤ t → StummK mP (mK t) := by
  intro t ht f hf
  have h0 : t ≠ 0 := fun h => by rw [h] at ht; exact absurd ht (by decide)
  have h1 : t ≠ 1 := fun h => by rw [h] at ht; exact absurd ht (by decide)
  simp only [mK, if_neg h0, if_neg h1] at hf
  cases f <;> simp only [mKR, Bool.false_eq_true] at hf
  exact ⟨by decide, fun c => by cases c with
    | inl t => cases t <;> rfl
    | inr g => exact nomatch g⟩

/-- **The new footprint check passes.** -/
theorem mP_fussMehr : fussMehrB mP mSI mFs mK 2 = true := by decide

/-- **Both earlier checks refuse the program**: `hauptA`'s footprint holds
    `privA` (its own writes, `pruefeA`'s `requires`, the owed invariant),
    guarded by nothing, written by `hauptA`, protected by no lock. -/
theorem mP_fussS_falsch : fussSperreB mP mSI mFs = false := by decide

theorem mP_fussG_falsch : fussOrtGB mP mFs = false := by decide

theorem mP_fragmentG : programmImFragmentG mP mFs = true := by decide

theorem mP_fuss : ∀ f, FussS mP mSI (lokK mP mK) f := fussMehrB_ok mFs_voll mStumm mP_fussMehr

theorem mP_stufen : StufenM mP := stufenM_of_ok (stufenOk_ohne mP fun f => by cases f <;> rfl)

/-! ## 4. The user obligations -/

theorem mA_schreib {S : SperrInv mD} {O : Orakel mD} {U : Umwelt mD} {passes : Nat}
    {R : ∀ f : mD.Fn, World mD → Env mD (mD.params f) → RufAusgang f} (σ : World mD)
    (ρ : Env mD (mD.params mHauptA)) :
    ∃ σ2 : World mD, execEndH S O U passes R mRumpfA σ ρ =
        execEndH S O U passes R (.cons mLocksA mRestA) σ2 ρ ∧
      (σ2.slots MTab.privA 0 ()).n = 7 ∧ (σ2.slots MTab.privA 1 ()).n = 7 :=
  ⟨_, rfl, rfl, rfl⟩

theorem mInv_of_ens {κ σ2 : World mD} {ρk : Env mD (mD.params mSetze)}
    {v : ErgVal mD (mD.erg mSetze)} (h : EnsAmRueck mP mSetze κ σ2 ρk v) :
    mSI.inv () σ2.speicher = true := by
  have h' : (decide ((σ2.slots MTab.konto 0 ()).n = (σ2.slots MTab.konto 1 ()).n) &&
      decide ((σ2.slots MTab.konto 0 ()).n = (ρk.get .here).n)) = true := h
  simp only [Bool.and_eq_true] at h'
  exact h'.1

theorem mA_req {W : World mD} (h : (W.slots MTab.privA 0 ()).n = 7) :
    ReqAmEintritt mP mPruefeA W .nil := by
  show decide ((W.slots MTab.privA 0 ()).n = 7) = true
  simp only [h, decide_true]

theorem mA_lauf {O : Orakel mD} {U : Umwelt mD} (hU : HavocOk mSI U)
    {R : ∀ f : mD.Fn, World mD → Env mD (mD.params f) → RufAusgang f} (hR : RespektiertRahmen mP R)
    (σ : World mD) (ρ : Env mD (mD.params mHauptA)) {σ' : World mD} {v : ErgVal mD (mD.erg mHauptA)}
    (hrun : execEndH mSI O U 0 R mRumpfA σ ρ = .zurueck σ' v) :
    (σ'.slots MTab.privA 0 ()).n = 7 ∧ (σ'.slots MTab.privA 1 ()).n = 7 := by
  obtain ⟨σ2, e2, h20, h21⟩ := mA_schreib (S := mSI) (O := O) (U := U) (passes := 0) (R := R) σ ρ
  rw [e2] at hrun
  simp only [execEndH, mLocksA] at hrun
  erw [execStmtH_locks_eins] at hrun
  have hU2 : (U () σ2).slots MTab.privA = σ2.slots MTab.privA :=
    (hU () σ2).2.1 (.inl MTab.privA) (fun h => by have := List.mem_singleton.mp h; cases this)
  rcases execStmtH_call_fall (S := mSI) (O := O) (U := U) (passes := 0) (R := R)
    (l := false) (Γ := []) mSetze (.cons m30 .nil) mHpSetzeA rfl ((U () σ2).nimmt ()) ρ with
    ⟨σ1, v1, hR1, h1⟩ | ⟨e1, he1, h1⟩ | ⟨e1, h1⟩ <;> erw [h1] at hrun
  · have hf1 := (hR.2 _ _ _ _ _ hR1).1.1 MTab.privA rfl
    cases hi : mSI.inv () σ1.speicher with
    | false => simp only [freiH, hi, Bool.false_eq_true, if_false] at hrun; cases hrun
    | true =>
      simp only [freiH, hi, if_true] at hrun
      simp only [mRestA, execEndH] at hrun
      rcases execStmtH_call_fall (S := mSI) (O := O) (U := U) (passes := 0) (R := R)
        (l := false) (Γ := []) mPruefeA .nil mHpPruefe rfl (σ1.gibt ()) ρ with
        ⟨σ3, v3, hR3, h3⟩ | ⟨e3, he3, h3⟩ | ⟨e3, h3⟩ <;> erw [h3] at hrun
      · simp only [execEndH] at hrun
        cases hrun
        have hf3 := (hR.2 _ _ _ _ _ hR3).1.1 MTab.privA rfl
        have e0 : σ3.slots MTab.privA 0 () = σ2.slots MTab.privA 0 () :=
          (hf3 0 ()).trans ((hf1 0 ()).trans (congrFun (congrFun hU2 0) ()))
        have e1 : σ3.slots MTab.privA 1 () = σ2.slots MTab.privA 1 () :=
          (hf3 1 ()).trans ((hf1 1 ()).trans (congrFun (congrFun hU2 1) ()))
        exact ⟨by show (σ3.slots MTab.privA 0 ()).n = 7; rw [e0]; exact h20,
          by show (σ3.slots MTab.privA 1 ()).n = 7; rw [e1]; exact h21⟩
      · cases hrun
      · cases hrun
  · simp only [freiH] at hrun; cases hrun
  · simp only [freiH] at hrun; cases hrun

end Gabbro.Grammatik
