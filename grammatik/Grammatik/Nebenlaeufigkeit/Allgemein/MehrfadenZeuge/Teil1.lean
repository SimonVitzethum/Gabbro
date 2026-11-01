module

public import Grammatik.Nebenlaeufigkeit.Allgemein.Verklemmung
public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtSperreZeuge

@[expose] public section



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
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp only [List.not_mem_nil] at h
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
  .widen (by decide) (by decide) (.lit 0)

def mI1 {Γ : Ctx} {Λ : List (Res mD)} : Expr mD Γ Λ (.index 2) :=
  .widen (by decide) (by decide) (.lit 1)

def m7 {Γ : Ctx} {Λ : List (Res mD)} : Expr mD Γ Λ (.int 0 100) := .widen (by decide) (by decide) (.lit 7)
def m5 {Γ : Ctx} {Λ : List (Res mD)} : Expr mD Γ Λ (.int 0 100) := .widen (by decide) (by decide) (.lit 5)
def m30 {Γ : Ctx} {Λ : List (Res mD)} : Expr mD Γ Λ (.int 0 100) := .widen (by decide) (by decide) (.lit 30)
def m70 {Γ : Ctx} {Λ : List (Res mD)} : Expr mD Γ Λ (.int 0 100) := .widen (by decide) (by decide) (.lit 70)

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
  hk := by rw [hk]; exact ⟨[], List.Perm.refl [], by simp only [List.nil_sublist]⟩
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

/-- `hauptA`: `ensures privA[0] == 7` from the two writes (the lock's move
    and the callees' frames leave `privA` alone); the caller duty of both
    calls from the lock invariant at the acquire and from the frames; no
    `logik` outcome because the release check follows from `setze`'s
    `ensures`. -/
end Gabbro.Grammatik
