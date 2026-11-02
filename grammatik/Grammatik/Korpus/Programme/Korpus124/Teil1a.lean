module

public import Grammatik.Zielsatz.Kern.Proben
import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice

@[expose] public section



namespace Gabbro.Grammatik

namespace K124

/-! ## 1. The declaration -/

inductive KTab where
  | konto
  | privA
  | privB
  deriving DecidableEq

inductive KFn where
  | setze
  | hauptA
  | hauptB
  | pruefeA
  deriving DecidableEq

/-- A signature: parameters, result, signature locks, written tables. -/
def kSig (ps : List Ty) (e : Option Ty) (h : List Unit) (ts : List KTab) :
    Signatur KTab Empty Unit Empty where
  params := ps
  erg := e
  gruende := 0
  haelt := h
  schreibt := fun t => decide (t ∈ ts)
  gschreibt := fun e => (nomatch e)
  konsumiert := []
  produziert := []

def kBraucht : KTab → List (Unit ⊕ (Empty × Nat))
  | .konto => [.inl ()]
  | _ => []

def kGeteilt : KTab → Bool
  | .konto => true
  | _ => false

def kSigNr : Nat → Signatur KTab Empty Unit Empty
  | 0 => kSig [.int 0 100] none [()] [.konto]
  | 1 => kSig [] none [] [.konto, .privA]
  | 2 => kSig [] none [] [.konto, .privB]
  | 3 => kSig [] (some (.int 0 100)) [] []
  | _ => kSig [] none [] []

def kSigOf : KFn → Nat
  | .setze => 0
  | .hauptA => 1
  | .hauptB => 2
  | .pruefeA => 3

/-- The declaration of `beispiele/124`: tables `konto` (shared, guarded by the
    lock `L = ()`), `privA`, `privB` (not shared), two slots each, `Stand =
    u32 in 0 .. 100`; no global, no table invariant, no axiom, no register. -/
def kD : Deklaration where
  Tab := KTab
  decTab := inferInstance
  count := fun _ => 2
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .int 0 100
  erlaubt := fun _ _ _ _ => false
  tabNr := fun _ => none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun e => (nomatch e)
  nutzlast := fun e => (nomatch e)
  atomar := fun e => (nomatch e)
  geteilt := kGeteilt
  ggeteilt := fun e => (nomatch e)
  Lock := Unit
  decLock := inferInstance
  rang := fun _ => 0
  maskiert := fun _ => false
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => (nomatch e)
  braucht := kBraucht
  gbraucht := fun e => (nomatch e)
  eigner := fun _ => []
  Fn := KFn
  sig := kSigOf
  sigNr := kSigNr
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp only [List.not_mem_nil] at h
  Inv := Empty
  traeger := fun i => (nomatch i)
  invs := []
  Ax := Empty
  aparams := fun e => (nomatch e)
  aerg := fun e => (nomatch e)
  aschreibt := fun e => (nomatch e)
  agschreibt := fun e => (nomatch e)
  Reg := Empty
  rtyp := fun e => (nomatch e)
  rklasse := fun e => (nomatch e)
  spiegel := fun e => (nomatch e)
  rzusage := fun e => (nomatch e)
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun t h => by cases t <;> simp_all [kGeteilt, kBraucht]
  invarianten_gehalten := fun _ i => (nomatch i)
  ggeteilt_bewacht := fun e => (nomatch e)

def kSetze : kD.Fn := KFn.setze
def kHauptA : kD.Fn := KFn.hauptA
def kHauptB : kD.Fn := KFn.hauptB
def kPruefeA : kD.Fn := KFn.pruefeA

instance : DecidableEq kD.Fn := inferInstanceAs (DecidableEq KFn)

abbrev kL : List (Res kD) := [Res.held (D := kD) ()]

theorem kDarfK : darf kD KTab.konto kL := by
  intro w h
  have e : w = Sum.inl () := List.mem_singleton.mp h
  subst e
  exact List.mem_singleton.mpr rfl

theorem kDarfA (Λ : List (Res kD)) : darf kD KTab.privA Λ := fun _ h => (nomatch h)
theorem kDarfB (Λ : List (Res kD)) : darf kD KTab.privB Λ := fun _ h => (nomatch h)

def kI0 {Γ : Ctx} {Λ : List (Res kD)} : Expr kD Γ Λ (.index 2) :=
  .widen (by decide) (by decide) (.lit 0)

def kI1 {Γ : Ctx} {Λ : List (Res kD)} : Expr kD Γ Λ (.index 2) :=
  .widen (by decide) (by decide) (.lit 1)

def k7 {Γ : Ctx} {Λ : List (Res kD)} : Expr kD Γ Λ (.int 0 100) := .widen (by decide) (by decide) (.lit 7)
def k5 {Γ : Ctx} {Λ : List (Res kD)} : Expr kD Γ Λ (.int 0 100) := .widen (by decide) (by decide) (.lit 5)
def k30 {Γ : Ctx} {Λ : List (Res kD)} : Expr kD Γ Λ (.int 0 100) := .widen (by decide) (by decide) (.lit 30)
def k70 {Γ : Ctx} {Λ : List (Res kD)} : Expr kD Γ Λ (.int 0 100) := .widen (by decide) (by decide) (.lit 70)

/-- `konto[0] == konto[1]` (the lock invariant), at the holdings `kL`. -/
def kGleich {Γ : Ctx} : Expr kD Γ kL .bool :=
  .eq (.slot KTab.konto () kI0 kDarfK) (.slot KTab.konto () kI1 kDarfK)

/-- `privA[0] == 7`. -/
def kA7 {Γ : Ctx} {Λ : List (Res kD)} : Expr kD Γ Λ .bool :=
  .eq (.slot KTab.privA () kI0 (kDarfA Λ)) k7

/-! ## 2. The program -/

/-- The call-site typing of every call. -/
theorem kHp (caller callee : kD.Fn) {Λ : List (Res kD)}
    (hw : ∀ t, (kD.signatur callee).schreibt t = true → (vertragVon kD caller).schreibt t = true)
    (hh : ∀ L, L ∈ (kD.signatur callee).haelt → Res.held L ∈ Λ)
    (hx : ∀ L, Res.held L ∈ Λ → L ∈ (kD.signatur callee).haelt)
    (hk : (kD.signatur callee).konsumiert = []) (hbc : (kD.signatur caller).boden = none) :
    RufPasst kD (vertragVon kD caller) (kD.signatur callee) Λ where
  hw := hw
  hg := fun g => (nomatch g)
  hb := fun c hc => by
    have : (vertragVon kD caller).boden = (kD.signatur caller).boden := rfl
    rw [this, hbc] at hc; cases hc
  hk := by
    unfold Signatur.inputMarks
    rw [hk, OwnerFlow.empty_of_empty (kD.signatur callee).owner]
    exact ⟨[], List.Perm.refl [], by simp only [List.nil_sublist]⟩
  hh := hh
  hx := fun L hL hn => absurd (hx L hL) hn

theorem kHpSetzeA : RufPasst kD (vertragVon kD kHauptA) (kD.signatur kSetze) kL :=
  kHp kHauptA kSetze (fun t h => by cases t <;> simp_all [kD, kSetze, kHauptA, Deklaration.signatur,
    kSigNr, kSigOf, kSig, vertragVon, Vertrag.vonSig])
    (fun L _ => by cases L; exact List.mem_singleton.mpr rfl)
    (fun L _ => by cases L; exact List.mem_singleton.mpr rfl) rfl rfl

theorem kHpSetzeB : RufPasst kD (vertragVon kD kHauptB) (kD.signatur kSetze) kL :=
  kHp kHauptB kSetze (fun t h => by cases t <;> simp_all [kD, kSetze, kHauptB, Deklaration.signatur,
    kSigNr, kSigOf, kSig, vertragVon, Vertrag.vonSig])
    (fun L _ => by cases L; exact List.mem_singleton.mpr rfl)
    (fun L _ => by cases L; exact List.mem_singleton.mpr rfl) rfl rfl

theorem kHpPruefe : RufPasst kD (vertragVon kD kHauptA) (kD.signatur kPruefeA) [] :=
  kHp kHauptA kPruefeA (fun t h => by cases t <;> simp_all [kD, kPruefeA, Deklaration.signatur,
    kSigNr, kSigOf, kSig])
    (fun L h => nomatch h) (fun L h => nomatch h) rfl rfl

/-- `setze(x)`: `konto.slots[0].stand = x; konto.slots[1].stand = x;`. -/
def kRumpfSetze : Endblock kD (vertragVon kD kSetze) false [.int 0 100] kL :=
  .cons (.assignSlot KTab.konto () kI0 (.var .here) rfl kDarfK)
    (.cons (.assignSlot KTab.konto () kI1 (.var .here) rfl kDarfK) (.ret .empty (by rfl)))

/-- `pruefeA()`: `return privA.slots[0].stand;`. -/
def kRumpfP : Endblock kD (vertragVon kD kPruefeA) false [] [] :=
  .ret (.val (.slot KTab.privA () kI0 (kDarfA _))) List.Perm.nil

/-- `privA.slots[0].stand = 7;` -/
def kA0 : Stmt kD (vertragVon kD kHauptA) false [] [] [] :=
  .assignSlot KTab.privA () kI0 k7 rfl (kDarfA _)

/-- `privA.slots[1].stand = 7;` -/
def kA1 : Stmt kD (vertragVon kD kHauptA) false [] [] [] :=
  .assignSlot KTab.privA () kI1 k7 rfl (kDarfA _)


end K124
end Gabbro.Grammatik
