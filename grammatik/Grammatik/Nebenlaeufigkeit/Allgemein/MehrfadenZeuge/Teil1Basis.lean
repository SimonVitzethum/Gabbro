/-
  File:      Grammatik/MehrfadenZeuge.lean
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
  passt := fun _ _ => false
  passt_ok := fun _ _ h => absurd h Bool.false_ne_true
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp only [List.not_mem_nil] at h
  Inv := Unit
  traeger := fun _ => [.inl .privA]
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
  invarianten_gehalten := fun _ _ _ c hc L hL => by
    simp only [List.mem_singleton] at hc
    subst hc
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
  hk := by
    unfold Signatur.inputMarks
    rw [hk, OwnerFlow.empty_of_empty (mD.signatur callee).owner]
    exact ⟨[], List.Perm.refl [], by simp only [List.nil_sublist]⟩
  hh := hh
  hx := fun L hL hn => absurd (hx L hL) hn
  ownerReady := OwnerFlow.escrowReady_of_empty _ _ _ _
    (OwnerFlow.empty_of_empty (mD.signatur callee).owner)

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

end Gabbro.Grammatik
