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

namespace K59

/-- Tables `Takte` and `Auftraege` of the source. -/
inductive KTab where
  | takte
  | auftraege
  deriving DecidableEq

/-- Locks `TAKT` (rank 0, masks irqs, protects `Takte`) and `RING` (rank 0,
    protects `Auftraege`). -/
inductive KLock where
  | takt
  | ring
  deriving DecidableEq

/-- Functions `zaehle`, `takt_verteiler`, `bearbeite`, `ruf_verteiler`. -/
inductive KFn where
  | zaehle
  | taktVert
  | bearbeite
  | rufVert
  deriving DecidableEq

/-- A signature: parameters, result, signature locks, written tables. -/
def kSig (ps : List Ty) (e : Option Ty) (h : List KLock) (ts : List KTab) :
    Signatur KTab Empty KLock Empty where
  params := ps
  erg := e
  gruende := 0
  haelt := h
  schreibt := fun t => decide (t ∈ ts)
  gschreibt := fun e => (nomatch e)
  konsumiert := []
  produziert := []

def kBraucht : KTab → List (KLock ⊕ (Empty × Nat))
  | .takte => [.inl .takt]
  | .auftraege => [.inl .ring]

/-- Both tables are shared, each guarded by its lock. -/
def kGeteilt : KTab → Bool
  | _ => true

def kRang : KLock → Int
  | .takt => 0
  | .ring => 0

/-- Only `TAKT` masks irqs -- the source's one-word difference from gift 460. -/
def kMaskiert : KLock → Bool
  | .takt => true
  | .ring => false

def kSigNr : Nat → Signatur KTab Empty KLock Empty
  | 0 => kSig [Ty.index 64] none [.takt] [.takte]
  | 1 => kSig [] none [] [.takte]
  | 2 => kSig [Ty.index 16] none [.ring] [.auftraege]
  | 3 => kSig [] none [] [.auftraege]
  | _ => kSig [] none [] []

def kSigOf : KFn → Nat
  | .zaehle => 0
  | .taktVert => 1
  | .bearbeite => 2
  | .rufVert => 3

/-- The declaration of `beispiele/59`: tables `Takte` (64 slots) and
    `Auftraege` (16 slots), `stand = u64`, each shared and guarded by its
    lock; no global, no table invariant, no axiom, no register. -/
def kD : Deklaration where
  Tab := KTab
  decTab := inferInstance
  count
    | .takte => 64
    | .auftraege => 16
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .int 0 18446744073709551615
  erlaubt := fun _ _ _ _ => false
  tabNr := fun _ => none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun e => (nomatch e)
  nutzlast := fun e => (nomatch e)
  atomar := fun e => (nomatch e)
  geteilt := kGeteilt
  ggeteilt := fun e => (nomatch e)
  Lock := KLock
  decLock := inferInstance
  rang := kRang
  maskiert := kMaskiert
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

def kZaehle : kD.Fn := KFn.zaehle
def kTaktVert : kD.Fn := KFn.taktVert
def kBearbeite : kD.Fn := KFn.bearbeite
def kRufVert : kD.Fn := KFn.rufVert

instance : DecidableEq kD.Fn := inferInstanceAs (DecidableEq KFn)
instance : DecidableEq kD.Lock := inferInstanceAs (DecidableEq KLock)

abbrev kLT : List (Res kD) := [Res.held (D := kD) KLock.takt]
abbrev kLR : List (Res kD) := [Res.held (D := kD) KLock.ring]

theorem kDarfTakte : darf kD KTab.takte kLT := by
  intro w h
  change w ∈ ([Sum.inl KLock.takt] : List (KLock ⊕ (Empty × Nat))) at h
  have e : w = Sum.inl KLock.takt := List.mem_singleton.mp h
  subst e
  exact List.mem_singleton.mpr rfl

theorem kDarfAuftr : darf kD KTab.auftraege kLR := by
  intro w h
  change w ∈ ([Sum.inl KLock.ring] : List (KLock ⊕ (Empty × Nat))) at h
  have e : w = Sum.inl KLock.ring := List.mem_singleton.mp h
  subst e
  exact List.mem_singleton.mpr rfl

/-- The index literal `0` as an index into `Takte` / `Auftraege`. -/
def kJ0T {Γ : Ctx} {Λ : List (Res kD)} : Expr kD Γ Λ (Ty.index 64) :=
  .widen (by decide) (by decide) (.lit 0)

def kJ0U {Γ : Ctx} {Λ : List (Res kD)} : Expr kD Γ Λ (Ty.index 16) :=
  .widen (by decide) (by decide) (.lit 0)

/-- The constant both leaves write. -/
def kEins {Γ : Ctx} {Λ : List (Res kD)} : Expr kD Γ Λ (.int 0 18446744073709551615) :=
  .widen (by decide) (by decide) (.lit 1)

/-- The call-site typing of every call. -/
theorem kHaeltZaehle : (kD.signatur kZaehle).haelt = [KLock.takt] := by rfl

theorem kHaeltBearbeite : (kD.signatur kBearbeite).haelt = [KLock.ring] := by rfl

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

theorem kHpZaehle : RufPasst kD (vertragVon kD kTaktVert) (kD.signatur kZaehle) kLT :=
  kHp kTaktVert kZaehle (fun t h => by cases t <;> simp_all [kD, kZaehle, kTaktVert, Deklaration.signatur,
    kSigNr, kSigOf, kSig, vertragVon, Vertrag.vonSig])
    (fun L hL => by cases L with
      | takt => exact List.mem_singleton.mpr rfl
      | ring => rw [kHaeltZaehle] at hL; exact KLock.noConfusion (List.mem_singleton.mp hL))
    (fun L hL => by
      have h2 : Res.held L = Res.held KLock.takt := List.mem_singleton.mp hL
      have h3 : L = KLock.takt := by cases h2; rfl
      rw [h3, kHaeltZaehle]; exact List.mem_singleton.mpr rfl) rfl rfl

theorem kHpBearbeite : RufPasst kD (vertragVon kD kRufVert) (kD.signatur kBearbeite) kLR :=
  kHp kRufVert kBearbeite (fun t h => by cases t <;> simp_all [kD, kBearbeite, kRufVert, Deklaration.signatur,
    kSigNr, kSigOf, kSig, vertragVon, Vertrag.vonSig])
    (fun L hL => by cases L with
      | takt => rw [kHaeltBearbeite] at hL; exact KLock.noConfusion (List.mem_singleton.mp hL)
      | ring => exact List.mem_singleton.mpr rfl)
    (fun L hL => by
      have h2 : Res.held L = Res.held KLock.ring := List.mem_singleton.mp hL
      have h3 : L = KLock.ring := by cases h2; rfl
      rw [h3, kHaeltBearbeite]; exact List.mem_singleton.mpr rfl) rfl rfl

end K59
end Gabbro.Grammatik
