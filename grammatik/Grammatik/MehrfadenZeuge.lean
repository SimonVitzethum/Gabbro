/-
  File:      Grammatik/MehrfadenZeuge.lean
  Subject:   THE WITNESS for the three concurrency repairs of 2026-09-14
             (SATZKARTE §16): two ACTIVE threads, each writing its OWN
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
import Grammatik.Verklemmung
import Grammatik.ZielOrtSperreZeuge

namespace Gabbro.Grammatik

/-! ## 1. The declaration -/

inductive MTab where
  | konto
  | privA
  | privB
  deriving DecidableEq

inductive MFn where
  | setze
  | hauptA
  | hauptB
  | pruefeA
  | ruhe
  deriving DecidableEq

/-- A signature: parameters, signature locks, written tables. -/
def mSig (ps : List Ty) (h : List Unit) (ts : List MTab) : Signatur MTab Empty Unit Empty where
  params := ps
  erg := none
  gruende := 0
  haelt := h
  schreibt := fun t => decide (t ∈ ts)
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

def mBraucht : MTab → List (Unit ⊕ (Empty × Nat))
  | .konto => [.inl ()]
  | _ => []

def mGeteilt : MTab → Bool
  | .konto => true
  | _ => false

def mSigNr : Nat → Signatur MTab Empty Unit Empty
  | 0 => mSig [.int 0 100] [()] [.konto]
  | 1 => mSig [] [] [.konto, .privA]
  | 2 => mSig [] [] [.konto, .privB]
  | _ => mSig [] [] []

def mSigOf : MFn → Nat
  | .setze => 0
  | .hauptA => 1
  | .hauptB => 2
  | .pruefeA => 3
  | .ruhe => 4

/-- The declaration of the witness. -/
def mD : Deklaration where
  Tab := MTab
  decTab := inferInstance
  count := fun _ => 2
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .int 0 100
  erlaubt := fun _ _ _ _ => false
  tabNr := fun _ => none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun e => nomatch e
  nutzlast := fun e => nomatch e
  atomar := fun e => nomatch e
  geteilt := mGeteilt
  ggeteilt := fun e => nomatch e
  Lock := Unit
  decLock := inferInstance
  rang := fun _ => 0
  maskiert := fun _ => false
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := mBraucht
  gbraucht := fun e => nomatch e
  eigner := fun _ => []
  Fn := MFn
  sig := mSigOf
  sigNr := mSigNr
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp at h
  Inv := Unit
  traeger := fun _ => [.privA]
  invs := [()]
  Ax := Empty
  aparams := fun e => nomatch e
  aerg := fun e => nomatch e
  aschreibt := fun e => nomatch e
  agschreibt := fun e => nomatch e
  Reg := Empty
  rtyp := fun e => nomatch e
  rklasse := fun e => nomatch e
  spiegel := fun e => nomatch e
  rzusage := fun e => nomatch e
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun t h => by cases t <;> simp_all [mGeteilt, mBraucht]
  invarianten_gehalten := fun _ _ _ t ht L hL => by
    simp only [List.mem_singleton] at ht
    subst ht
    cases hL
  ggeteilt_bewacht := fun e => nomatch e

def mSetze : mD.Fn := MFn.setze
def mHauptA : mD.Fn := MFn.hauptA
def mHauptB : mD.Fn := MFn.hauptB
def mPruefeA : mD.Fn := MFn.pruefeA
def mRuhe : mD.Fn := MFn.ruhe

instance : DecidableEq mD.Fn := inferInstanceAs (DecidableEq MFn)

abbrev mL : List (Res mD) := [Res.held (D := mD) ()]

theorem mDarfK : darf mD MTab.konto mL := by
  intro w h
  have e : w = Sum.inl () := List.mem_singleton.mp h
  subst e
  exact List.mem_singleton.mpr rfl

theorem mDarfA (Λ : List (Res mD)) : darf mD MTab.privA Λ := fun _ h => nomatch h
theorem mDarfB (Λ : List (Res mD)) : darf mD MTab.privB Λ := fun _ h => nomatch h

def mI0 {Γ : Ctx} {Λ : List (Res mD)} : Expr mD Γ Λ (.index 2) :=
  .weiter (by decide) (by decide) (.lit 0)

def mI1 {Γ : Ctx} {Λ : List (Res mD)} : Expr mD Γ Λ (.index 2) :=
  .weiter (by decide) (by decide) (.lit 1)

def m7 {Γ : Ctx} {Λ : List (Res mD)} : Expr mD Γ Λ (.int 0 100) := .weiter (by decide) (by decide) (.lit 7)
def m5 {Γ : Ctx} {Λ : List (Res mD)} : Expr mD Γ Λ (.int 0 100) := .weiter (by decide) (by decide) (.lit 5)
def m30 {Γ : Ctx} {Λ : List (Res mD)} : Expr mD Γ Λ (.int 0 100) := .weiter (by decide) (by decide) (.lit 30)
def m70 {Γ : Ctx} {Λ : List (Res mD)} : Expr mD Γ Λ (.int 0 100) := .weiter (by decide) (by decide) (.lit 70)

/-- `konto[0] == konto[1]`, at the holdings `mL`. -/
def mGleich {Γ : Ctx} : Expr mD Γ mL .bool :=
  .eq (.slot MTab.konto () mI0 mDarfK) (.slot MTab.konto () mI1 mDarfK)

/-- `privA[0] == 7`. -/
def mA7 {Γ : Ctx} {Λ : List (Res mD)} : Expr mD Γ Λ .bool :=
  .eq (.slot MTab.privA () mI0 (mDarfA Λ)) m7

/-- `privA[0] == privA[1]`. -/
def mAGleich {Γ : Ctx} {Λ : List (Res mD)} : Expr mD Γ Λ .bool :=
  .eq (.slot MTab.privA () mI0 (mDarfA Λ)) (.slot MTab.privA () mI1 (mDarfA Λ))

/-! ## 2. The program -/

/-- The call-site typing of every call in the witness. -/
theorem mHp (caller callee : mD.Fn) {Λ : List (Res mD)}
    (hw : ∀ t, (mD.signatur callee).schreibt t = true → (vertragVon mD caller).schreibt t = true)
    (hh : ∀ L, L ∈ (mD.signatur callee).haelt → Res.held L ∈ Λ)
    (hx : ∀ L, Res.held L ∈ Λ → L ∈ (mD.signatur callee).haelt)
    (hk : (mD.signatur callee).konsumiert = []) (hbc : (mD.signatur caller).boden = none) :
    RufPasst mD (vertragVon mD caller) (mD.signatur callee) Λ where
  hw := hw
  hg := fun g => nomatch g
  hb := fun c hc => by
    have : (vertragVon mD caller).boden = (mD.signatur caller).boden := rfl
    rw [this, hbc] at hc; cases hc
  hk := by rw [hk]; exact ⟨[], List.Perm.refl [], by simp⟩
  hh := hh
  hx := fun L hL hn => absurd (hx L hL) hn

theorem mHpSetzeA : RufPasst mD (vertragVon mD mHauptA) (mD.signatur mSetze) mL :=
  mHp mHauptA mSetze (fun t h => by cases t <;> simp_all [mD, mSetze, mHauptA, Deklaration.signatur,
    mSigNr, mSigOf, mSig, vertragVon, Vertrag.vonSig])
    (fun L _ => by cases L; exact List.mem_singleton.mpr rfl)
    (fun L _ => by cases L; exact List.mem_singleton.mpr rfl) rfl rfl

theorem mHpSetzeB : RufPasst mD (vertragVon mD mHauptB) (mD.signatur mSetze) mL :=
  mHp mHauptB mSetze (fun t h => by cases t <;> simp_all [mD, mSetze, mHauptB, Deklaration.signatur,
    mSigNr, mSigOf, mSig, vertragVon, Vertrag.vonSig])
    (fun L _ => by cases L; exact List.mem_singleton.mpr rfl)
    (fun L _ => by cases L; exact List.mem_singleton.mpr rfl) rfl rfl

theorem mHpPruefe : RufPasst mD (vertragVon mD mHauptA) (mD.signatur mPruefeA) [] :=
  mHp mHauptA mPruefeA (fun t h => by cases t <;> simp_all [mD, mPruefeA, Deklaration.signatur,
    mSigNr, mSigOf, mSig])
    (fun L h => nomatch h) (fun L h => nomatch h) rfl rfl

/-- `setze(x)`: `konto[0] = x; konto[1] = x; return`. -/
def mRumpfSetze : Endblock mD (vertragVon mD mSetze) false [.int 0 100] mL :=
  .cons (.assignSlot MTab.konto () mI0 (.var .hier) rfl mDarfK)
    (.cons (.assignSlot MTab.konto () mI1 (.var .hier) rfl mDarfK) (.ret .keine (by rfl)))

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
  .cons (.call mPruefeA .nil mHpPruefe rfl) (.ret .keine List.Perm.nil)

/-- `hauptA`: `privA[0] = 7; privA[1] = 7; locks { setze(30) }; pruefeA(); return`. -/
def mRumpfA : Endblock mD (vertragVon mD mHauptA) false [] [] :=
  .cons (.assignSlot MTab.privA () mI0 m7 rfl (mDarfA _))
    (.cons (.assignSlot MTab.privA () mI1 m7 rfl (mDarfA _))
      (.cons mLocksA mRestA))

/-- `hauptB`: `privB[0] = 5; locks { setze(70) }; return`. -/
def mRumpfB : Endblock mD (vertragVon mD mHauptB) false [] [] :=
  .cons (.assignSlot MTab.privB () mI0 m5 rfl (mDarfB _))
    (.cons mLocksB (.ret .keine List.Perm.nil))

/-- The program. -/
def mP : Programm mD where
  invariante := fun _ => mAGleich
  requires
    | .setze => mGleich
    | .pruefeA => mA7
    | _ => .wahr
  ensures
    | .setze => .und mGleich (.eq (.slot MTab.konto () mI0 mDarfK) (.var .hier))
    | .hauptA => mA7
    | _ => .wahr
  rumpf
    | .setze => mRumpfSetze
    | .hauptA => mRumpfA
    | .hauptB => mRumpfB
    | .pruefeA => .ret .keine List.Perm.nil
    | .ruhe => .ret .keine List.Perm.nil

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
  cases f <;> simp [mKR] at hf
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
      decide ((σ2.slots MTab.konto 0 ()).n = (ρk.get .hier).n)) = true := h
  simp only [Bool.and_eq_true] at h'
  exact h'.1

theorem mA_req {W : World mD} (h : (W.slots MTab.privA 0 ()).n = 7) :
    ReqAmEintritt mP mPruefeA W .nil := by
  show decide ((W.slots MTab.privA 0 ()).n = 7) = true
  simp [h]

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

/-- `hauptA`: `ensures privA[0] == 7` from the two writes (the lock's move
    and the callees' frames leave `privA` alone); the caller duty of both
    calls from the lock invariant at the acquire and from the frames; no
    `logik` outcome because the release check follows from `setze`'s
    `ensures`. -/
theorem mP_koerper_A : KoerperGutS mP 0 (axWahr mD) mSI mHauptA := by
  have hr : mP.rumpf mHauptA = mRumpfA := rfl
  refine ⟨fun O' _ _ _ U hU R hR hOV σ ρ _ => ⟨fun σ' v hrun => ?_, fun g hrun => ?_⟩,
    fun O' _ _ _ U hU R hR hOL σ ρ _ e hrun => ?_⟩
  · rw [hr] at hrun
    have h := (mA_lauf hU hR σ ρ hrun).1
    show decide ((σ'.slots MTab.privA 0 ()).n = 7) = true
    simp [h]
  · rw [hr] at hrun
    obtain ⟨σ2, e2, h20, _⟩ := mA_schreib (S := mSI) (O := O') (U := U) (passes := 0)
      (R := torRuf mP R) σ ρ
    erw [e2] at hrun
    simp only [execEndH, mLocksA] at hrun
    erw [execStmtH_locks_eins] at hrun
    have hU2 : (U () σ2).slots MTab.privA = σ2.slots MTab.privA :=
      (hU () σ2).2.1 (.inl MTab.privA) (fun h => by have := List.mem_singleton.mp h; cases this)
    have hreq : ReqAmEintritt mP mSetze (((U () σ2).nimmt ()).lese mL [])
        (evalArgs (((U () σ2).nimmt ()).lese mL []) (Args.cons (Λ := mL) (Γ := []) m30 .nil)
          (((U () σ2).nimmt ()).lese mL []) ρ) := (hU () σ2).2.2
    have htor : ∀ w a, ReqAmEintritt mP mSetze w a → torRuf mP R mSetze w a = R mSetze w a :=
      fun _ _ h => if_pos h
    rcases execStmtH_call_fall (S := mSI) (O := O') (U := U) (passes := 0) (R := torRuf mP R)
      (l := false) (Γ := []) mSetze (.cons m30 .nil) mHpSetzeA rfl ((U () σ2).nimmt ()) ρ with
      ⟨σ1, v1, hR1, h1⟩ | ⟨e1, he1, h1⟩ | ⟨e1, h1⟩ <;> erw [h1] at hrun
    · have hR1' := (htor _ _ hreq).symm.trans hR1
      have hf1 := (hR.2 _ _ _ _ _ hR1').1.1 MTab.privA rfl
      cases hi : mSI.inv () σ1.speicher with
      | false => simp only [freiH, hi, Bool.false_eq_true, if_false] at hrun; cases hrun
      | true =>
        simp only [freiH, hi, if_true] at hrun
        simp only [mRestA, execEndH] at hrun
        have e0 : ((σ1.gibt ()).lese [] []).slots MTab.privA 0 () = σ2.slots MTab.privA 0 () :=
          (hf1 0 ()).trans (congrFun (congrFun hU2 0) ())
        have hreq3 : ReqAmEintritt mP mPruefeA ((σ1.gibt ()).lese [] []) .nil :=
          mA_req (by rw [e0]; exact h20)
        rcases execStmtH_call_fall (S := mSI) (O := O') (U := U) (passes := 0) (R := torRuf mP R)
          (l := false) (Γ := []) mPruefeA .nil mHpPruefe rfl (σ1.gibt ()) ρ with
          ⟨σ3, v3, hR3, h3⟩ | ⟨e3, he3, h3⟩ | ⟨e3, h3⟩ <;> erw [h3] at hrun
        · cases hrun
        · cases hrun
          have htor3 : torRuf mP R mPruefeA ((σ1.gibt ()).lese [] []) .nil =
              R mPruefeA ((σ1.gibt ()).lese [] []) .nil := if_pos hreq3
          exact hOV _ _ _ _ (htor3.symm.trans he3) g rfl
        · cases hrun
    · simp only [freiH] at hrun
      cases hrun
      exact hOV _ _ _ _ ((htor _ _ hreq).symm.trans he1) g rfl
    · simp only [freiH] at hrun; cases hrun
  · rw [hr] at hrun
    obtain ⟨σ2, e2, _, _⟩ := mA_schreib (S := mSI) (O := O') (U := U) (passes := 0) (R := R) σ ρ
    erw [e2] at hrun
    simp only [execEndH, mLocksA] at hrun
    erw [execStmtH_locks_eins] at hrun
    have hreq : ReqAmEintritt mP mSetze (((U () σ2).nimmt ()).lese mL [])
        (evalArgs (((U () σ2).nimmt ()).lese mL []) (Args.cons (Λ := mL) (Γ := []) m30 .nil)
          (((U () σ2).nimmt ()).lese mL []) ρ) := (hU () σ2).2.2
    rcases execStmtH_call_fall (S := mSI) (O := O') (U := U) (passes := 0) (R := R)
      (l := false) (Γ := []) mSetze (.cons m30 .nil) mHpSetzeA rfl ((U () σ2).nimmt ()) ρ with
      ⟨σ1, v1, hR1, h1⟩ | ⟨e1, he1, h1⟩ | ⟨e1, h1⟩ <;> erw [h1] at hrun
    · have hinv := mInv_of_ens (hR.1 _ _ _ hreq σ1 v1 hR1)
      simp only [freiH, hinv, if_true] at hrun
      simp only [mRestA, execEndH] at hrun
      rcases execStmtH_call_fall (S := mSI) (O := O') (U := U) (passes := 0) (R := R)
        (l := false) (Γ := []) mPruefeA .nil mHpPruefe rfl (σ1.gibt ()) ρ with
        ⟨σ3, v3, hR3, h3⟩ | ⟨e3, he3, h3⟩ | ⟨e3, h3⟩ <;> erw [h3] at hrun
      · cases hrun
      · cases hrun
        exact hOL _ _ _ _ he3
      · cases hrun
    · simp only [freiH] at hrun
      cases hrun
      exact hOL _ _ _ _ he1
    · simp only [freiH] at hrun; cases hrun

/-- `hauptA` owes the invariant `privA[0] == privA[1]` and meets it. -/
theorem mP_inv_A : InvGutS mP 0 (axWahr mD) mSI mHauptA := by
  intro O' _ _ _ U hU R hR _ σ ρ _ σ' v hrun i _ _
  have hr : mP.rumpf mHauptA = mRumpfA := rfl
  rw [hr] at hrun
  have h := mA_lauf hU hR σ ρ hrun
  cases i
  show decide ((σ'.slots MTab.privA 0 ()).n = (σ'.slots MTab.privA 1 ()).n) = true
  simp [h.1, h.2]

theorem mB_schreib {S : SperrInv mD} {O : Orakel mD} {U : Umwelt mD} {passes : Nat}
    {R : ∀ f : mD.Fn, World mD → Env mD (mD.params f) → RufAusgang f} (σ : World mD)
    (ρ : Env mD (mD.params mHauptB)) :
    ∃ σ2 : World mD, execEndH S O U passes R mRumpfB σ ρ =
        execEndH S O U passes R (.cons mLocksB (.ret .keine List.Perm.nil)) σ2 ρ :=
  ⟨_, rfl⟩

/-- `hauptB`: the caller duty from the lock invariant at the acquire; the
    release check from `setze`'s `ensures`. -/
theorem mP_koerper_B : KoerperGutS mP 0 (axWahr mD) mSI mHauptB := by
  have hr : mP.rumpf mHauptB = mRumpfB := rfl
  refine ⟨fun O' _ _ _ U hU R hR hOV σ ρ _ => ⟨fun σ' v _ => rfl, fun g hrun => ?_⟩,
    fun O' _ _ _ U hU R hR hOL σ ρ _ e hrun => ?_⟩
  · rw [hr] at hrun
    obtain ⟨σ2, e2⟩ := mB_schreib (S := mSI) (O := O') (U := U) (passes := 0)
      (R := torRuf mP R) σ ρ
    erw [e2] at hrun
    simp only [execEndH, mLocksB] at hrun
    erw [execStmtH_locks_eins] at hrun
    have hreq : ReqAmEintritt mP mSetze (((U () σ2).nimmt ()).lese mL [])
        (evalArgs (((U () σ2).nimmt ()).lese mL []) (Args.cons (Λ := mL) (Γ := []) m70 .nil)
          (((U () σ2).nimmt ()).lese mL []) ρ) := (hU () σ2).2.2
    rcases execStmtH_call_fall (S := mSI) (O := O') (U := U) (passes := 0) (R := torRuf mP R)
      (l := false) (Γ := []) mSetze (.cons m70 .nil) mHpSetzeB rfl ((U () σ2).nimmt ()) ρ with
      ⟨σ1, v1, hR1, h1⟩ | ⟨e1, he1, h1⟩ | ⟨e1, h1⟩ <;> erw [h1] at hrun
    · cases hi : mSI.inv () σ1.speicher with
      | false => simp only [freiH, hi, Bool.false_eq_true, if_false] at hrun; cases hrun
      | true => simp only [freiH, hi, if_true] at hrun; cases hrun
    · simp only [freiH] at hrun
      cases hrun
      have htor : torRuf mP R mSetze _ _ = R mSetze _ _ := if_pos hreq
      exact hOV _ _ _ _ (htor.symm.trans he1) g rfl
    · simp only [freiH] at hrun; cases hrun
  · rw [hr] at hrun
    obtain ⟨σ2, e2⟩ := mB_schreib (S := mSI) (O := O') (U := U) (passes := 0) (R := R) σ ρ
    erw [e2] at hrun
    simp only [execEndH, mLocksB] at hrun
    erw [execStmtH_locks_eins] at hrun
    have hreq : ReqAmEintritt mP mSetze (((U () σ2).nimmt ()).lese mL [])
        (evalArgs (((U () σ2).nimmt ()).lese mL []) (Args.cons (Λ := mL) (Γ := []) m70 .nil)
          (((U () σ2).nimmt ()).lese mL []) ρ) := (hU () σ2).2.2
    rcases execStmtH_call_fall (S := mSI) (O := O') (U := U) (passes := 0) (R := R)
      (l := false) (Γ := []) mSetze (.cons m70 .nil) mHpSetzeB rfl ((U () σ2).nimmt ()) ρ with
      ⟨σ1, v1, hR1, h1⟩ | ⟨e1, he1, h1⟩ | ⟨e1, h1⟩ <;> erw [h1] at hrun
    · have hinv := mInv_of_ens (hR.1 _ _ _ hreq σ1 v1 hR1)
      simp only [freiH, hinv, if_true] at hrun
      cases hrun
    · simp only [freiH] at hrun
      cases hrun
      exact hOL _ _ _ _ he1
    · simp only [freiH] at hrun; cases hrun

theorem mP_koerper_setze : KoerperGutS mP 0 (axWahr mD) mSI mSetze := by
  have hr : mP.rumpf mSetze = mRumpfSetze := rfl
  refine ⟨fun O' _ _ _ U _ R _ _ σ ρ _ => ⟨fun σ' v hrun => ?_, fun g hrun => ?_⟩,
    fun O' _ _ _ U _ R _ _ σ ρ _ e hrun => ?_⟩
  · rw [hr] at hrun
    simp only [mRumpfSetze, execEndH, execStmtH] at hrun
    cases hrun
    cases ρ with
    | cons x rest =>
      cases rest
      show wahr? (eval σ (mP.ensures mSetze) _ (ergEnv (mD.erg mSetze) () (Env.cons x Env.nil))) = true
      simp [mP, mSetze, mGleich, eval, World.lese, World.merke, World.schreibSlot,
        World.storeSlot, mI0, mI1, Zahl.weiter, wahr?, ergEnv]
      exact ⟨rfl, rfl⟩
  · rw [hr] at hrun
    simp only [mRumpfSetze, execEndH, execStmtH] at hrun
    cases hrun
  · rw [hr] at hrun
    simp only [mRumpfSetze, execEndH, execStmtH] at hrun
    cases hrun

theorem mP_koerper_leer (f : mD.Fn) (hf : f = mPruefeA ∨ f = mRuhe) :
    KoerperGutS mP 0 (axWahr mD) mSI f := by
  rcases hf with rfl | rfl <;>
  refine ⟨fun O' _ _ _ U _ R _ _ σ ρ _ => ⟨fun σ' v _ => rfl, fun g hrun => ?_⟩,
    fun O' _ _ _ U _ R _ _ σ ρ _ e hrun => ?_⟩ <;> cases hrun

theorem mP_koerper : ∀ f : mD.Fn, KoerperGutS mP 0 (axWahr mD) mSI f := by
  intro f
  cases f
  · exact mP_koerper_setze
  · exact mP_koerper_A
  · exact mP_koerper_B
  · exact mP_koerper_leer _ (Or.inl rfl)
  · exact mP_koerper_leer _ (Or.inr rfl)

theorem mP_inv : ∀ f : mD.Fn, InvGutS mP 0 (axWahr mD) mSI f := by
  intro f
  cases f
  · exact invGutS_ohne fun i _ => by cases i; rfl
  · exact mP_inv_A
  · exact invGutS_ohne fun i _ => by cases i; rfl
  · exact invGutS_ohne fun i _ => by cases i; rfl
  · exact invGutS_ohne fun i _ => by cases i; rfl


/-! ## 5. Every premise, jointly -/

def mO : Orakel mD where
  wirkt := fun a => nomatch a
  regLies := fun r => nomatch r
  regSchreib := fun r _ => nomatch r
  sichtbar := fun g => nomatch g

theorem mO_gut : GutO mO := fun a => nomatch a

theorem mO_lokal : RegLokal mO := ⟨(fun r _ _ _ => nomatch r), (fun g _ _ _ => nomatch g)⟩

/-- The start memory: every slot zero. -/
def mSp : Speicher mD := ⟨fun _ _ _ => ⟨0, by decide, by decide⟩, fun g => nomatch g⟩

theorem mP_start : StartGut mP mSp mInit := by
  intro t
  unfold mInit
  by_cases h0 : t = 0
  · rw [if_pos h0]; rfl
  · rw [if_neg h0]
    by_cases h1 : t = 1
    · rw [if_pos h1]; rfl
    · rw [if_neg h1]; rfl

/-- No start function holds a lock by signature. -/
theorem mInit_leer : ∀ t, mD.haelt (mInit t).1 = [] := by
  intro t
  unfold mInit
  by_cases h0 : t = 0
  · rw [if_pos h0]; rfl
  · rw [if_neg h0]
    by_cases h1 : t = 1
    · rw [if_pos h1]; rfl
    · rw [if_neg h1]; rfl

theorem mInit_exklusiv : StartExklusiv (D := mD) mInit := startExklusiv_ohne_haelt mInit mInit_leer

theorem mSI_start : ∀ L, mSI.inv L mSp = true := fun _ => rfl

def mE0 : Ereignis mD := .gibt ()

/-- No body of the witness contains a `forever` loop: its obligation at
    budget `0` is its obligation at every budget (`koerperGutS_alle`). -/
theorem mP_ohneEwig : ohneEwigB mP mFs = true := by decide

theorem mP_koerper_alle : ∀ (passes : Nat) (f : mD.Fn), KoerperGutS mP passes (axWahr mD) mSI f :=
  koerperGutS_alle mFs_voll mP_ohneEwig mP_koerper

theorem mP_inv_alle : ∀ (passes : Nat) (f : mD.Fn), InvGutS mP passes (axWahr mD) mSI f :=
  invGutS_alle mFs_voll mP_ohneEwig mP_inv

/-- **`mP_zertifiziert` -- every premise of the flagship
    `ziel_ort_mehrfaden_ende` holds on the two-writer program with private
    tables** (the obligations at EVERY `forever` budget), hence its
    conclusion on every reachable machine of every budget: contracts at
    every logged entry and return, the lock invariant of every free lock,
    no stop at a `logik` check, owed invariants at every logged return,
    and at every finished thread the start function's `ensures` and owed
    invariants. -/
theorem mP_zertifiziert : ∀ (passes : Nat) (M : RufMaschineG mD),
    RufErreichbarG mP mO passes (RufStartG mP mSp mInit) M →
      ((VertragAmOrtG mP M ∧ SperrInvG mSI M ∧ KeinLogikHaltG mO passes M ∧
        ∀ t : Faden, HeldGenau (M.faeden t).kopf.rest.2.2.1 (offen (M.faeden t).spur) →
          AnPruefungG M t → ∃ M', RufSchrittG mP mO passes M t M') ∧
      InvAmOrtG mP M) ∧ StartEndeG mP M :=
  ziel_ort_mehrfaden_ende mP mO (axWahr mD) mSI mFs mSp mInit mE0 mK mO_gut mO_lokal
    (axVertragO_wahr mO) axEnsLokal_wahr mSI_ok mFs_voll mP_fragmentG mAbg mWurzel mP_fuss
    mP_koerper_alle mP_start mSI_start mInit_exklusiv mP_inv_alle

/-- **`mP_verklemmungsfrei` -- every premise of the deadlock theorem holds
    on the witness**: on every reachable machine, if every unfinished thread
    waits for a lock another thread holds, every thread is finished. -/
theorem mP_verklemmungsfrei : ∀ M : RufMaschineG mD,
    RufErreichbarG mP mO 0 (RufStartG mP mSp mInit) M →
      (∀ t, ¬ FertigG M t → WartetG M t) → ∀ t, FertigG M t :=
  fun _ hr hW => keine_verklemmungG mO_gut mP_stufen mSp mInit mInit_leer [()]
    (fun L => by cases L; exact List.mem_singleton_self _) hr hW

/-- The rank invariant on every reachable machine of the witness. -/
theorem mP_rang : ∀ M : RufMaschineG mD,
    RufErreichbarG mP mO 0 (RufStartG mP mSp mInit) M → ∀ t, RangInvG (mInit t).1 (M.faeden t) :=
  fun _ hr => rangInvG_erreichbar mO_gut mP_stufen mSp mInit
    (fun t => by rw [startSpur, mInit_leer t]; exact List.nodup_nil) hr

/-- `ziel_ort_mehrfaden` (without the completion conjunct) on the witness,
    over every budget. -/
theorem mP_mehrfaden : ∀ (passes : Nat) (M : RufMaschineG mD),
    RufErreichbarG mP mO passes (RufStartG mP mSp mInit) M →
      (VertragAmOrtG mP M ∧ SperrInvG mSI M ∧ KeinLogikHaltG mO passes M ∧
        ∀ t : Faden, HeldGenau (M.faeden t).kopf.rest.2.2.1 (offen (M.faeden t).spur) →
          AnPruefungG M t → ∃ M', RufSchrittG mP mO passes M t M') ∧ InvAmOrtG mP M :=
  ziel_ort_mehrfaden mP mO (axWahr mD) mSI mFs mSp mInit mE0 mK mO_gut mO_lokal
    (axVertragO_wahr mO) axEnsLokal_wahr mSI_ok mFs_voll mP_fragmentG mAbg mWurzel mP_fuss
    mP_koerper_alle mP_start mSI_start mInit_exklusiv mP_inv_alle

theorem sP_ohneEwig : ohneEwigB sP sFs = true := by decide

/-- `ziel_ort_sperre_ende` (the old footprint check, with the completion
    conjunct) on the earlier two-writer program `sP`, over every budget:
    the two-writer witness of §14.5 carries over. -/
theorem sP_ende_zertifiziert : ∀ (passes : Nat) (M : RufMaschineG sD),
    RufErreichbarG sP sO passes (RufStartG sP sSp sInit) M →
      ((VertragAmOrtG sP M ∧ SperrInvG sS M ∧ KeinLogikHaltG sO passes M ∧
        ∀ t : Faden, HeldGenau (M.faeden t).kopf.rest.2.2.1 (offen (M.faeden t).spur) →
          AnPruefungG M t → ∃ M', RufSchrittG sP sO passes M t M') ∧ InvAmOrtG sP M) ∧
      StartEndeG sP M :=
  ziel_ort_sperre_ende sP sO (axWahr sD) sS sFs sSp sInit sE0 sO_gut sO_lokal
    (axVertragO_wahr sO) axEnsLokal_wahr sS_ok sFs_voll sP_fragmentG sP_fussS
    (koerperGutS_alle sFs_voll sP_ohneEwig sP_koerper) sP_start
    sS_start sInit_exklusiv (fun _ => invGutS_leer rfl)

#print axioms Gabbro.Grammatik.mP_mehrfaden
#print axioms Gabbro.Grammatik.sP_ende_zertifiziert
#print axioms Gabbro.Grammatik.mP_zertifiziert
#print axioms Gabbro.Grammatik.mP_verklemmungsfrei
#print axioms Gabbro.Grammatik.mP_fussMehr
#print axioms Gabbro.Grammatik.mP_fuss

end Gabbro.Grammatik
