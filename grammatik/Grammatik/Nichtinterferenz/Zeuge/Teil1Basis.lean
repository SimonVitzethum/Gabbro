module

public import Grammatik.Nichtinterferenz.Fluss

@[expose] public section



namespace Gabbro.Grammatik

namespace NIZeuge

/-! ## 1. The declaration -/

inductive NTab where
  | tabA
  | tabB
  deriving DecidableEq

inductive NGlob where
  | konfig
  | zaehler
  deriving DecidableEq

inductive NFn where
  | hauptA
  | hauptB
  | kern
  | ruhe
  | zaehlA
  | zaehlB
  | leck
  deriving DecidableEq

def nSig (ts : List NTab) (gs : List NGlob) : Signatur NTab NGlob Empty Empty where
  params := []
  erg := none
  gruende := 0
  haelt := []
  schreibt := fun t => decide (t ∈ ts)
  gschreibt := fun g => decide (g ∈ gs)
  konsumiert := []
  produziert := []

def nSigNr : Nat → Signatur NTab NGlob Empty Empty
  | 0 => nSig [.tabA] []
  | 1 => nSig [.tabB] []
  | 2 => nSig [] [.konfig]
  | 4 => nSig [] [.zaehler]
  | 5 => nSig [.tabB] []
  | 6 => nSig [.tabB] []
  | _ => nSig [] []

def nSigOf : NFn → Nat
  | .hauptA => 0
  | .hauptB => 1
  | .kern => 2
  | .ruhe => 3
  | .zaehlA => 4
  | .zaehlB => 5
  | .leck => 6

/-- The declaration of the two-tenant witness. -/
def nD : Deklaration where
  Tab := NTab
  decTab := inferInstance
  count := fun _ => 1
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .int 0 9
  erlaubt := fun _ _ _ _ => false
  tabNr := fun _ => none
  Glob := NGlob
  decGlob := inferInstance
  gtyp := fun _ => .int 0 9
  nutzlast := fun _ => []
  atomar := fun _ => true
  geteilt := fun _ => false
  ggeteilt := fun _ => false
  Lock := Empty
  decLock := inferInstance
  rang := fun e => nomatch e
  maskiert := fun e => nomatch e
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := fun _ => []
  gbraucht := fun _ => []
  eigner := fun _ => []
  Fn := NFn
  sig := nSigOf
  sigNr := nSigNr
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp only [List.not_mem_nil] at h
  Inv := Empty
  traeger := fun e => nomatch e
  invs := []
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
  geteilt_bewacht := fun _ h => by simp only [Bool.false_eq_true] at h
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun _ h => by simp only [Bool.false_eq_true] at h

instance : DecidableEq nD.Fn := inferInstanceAs (DecidableEq NFn)

theorem nDarf (t : nD.Tab) (Λ : List (Res nD)) : darf nD t Λ := fun _ h => nomatch h
theorem nGd (g : nD.Glob) (Λ : List (Res nD)) : gdarf nD g Λ := fun _ h => nomatch h

def nI0 {Γ : Ctx} {Λ : List (Res nD)} {t : nD.Tab} : Expr nD Γ Λ (.index (nD.count t)) :=
  .widen (by decide) (show (0 : Int) ≤ 1 - 1 by decide) (.lit 0)

def nW {Γ : Ctx} {Λ : List (Res nD)} (k : Int) (h0 : (0 : Int) ≤ k) (h9 : k ≤ 9) :
    Expr nD Γ Λ (.int 0 9) :=
  .widen h0 h9 (.lit k)

/-! ## 2. The program -/

def nRumpfA : Endblock nD (vertragVon nD NFn.hauptA) false [] [] :=
  .cons (.assignSlot NTab.tabA () nI0 (.glob NGlob.konfig (nGd _ _)) rfl (nDarf _ _))
    (.ret .empty List.Perm.nil)

def nRumpfB : Endblock nD (vertragVon nD NFn.hauptB) false [] [] :=
  .cons (.assignSlot NTab.tabB () nI0 (.glob NGlob.konfig (nGd _ _)) rfl (nDarf _ _))
    (.ret .empty List.Perm.nil)

def nKernS : Stmt nD (vertragVon nD NFn.kern) false [] [] [] :=
  .assignGlob NGlob.konfig (nW 3 (by decide) (by decide)) rfl (nGd _ _)

def nRumpfKern : Endblock nD (vertragVon nD NFn.kern) false [] [] :=
  .cons nKernS (.ret .empty List.Perm.nil)

def nRumpfZA : Endblock nD (vertragVon nD NFn.zaehlA) false [] [] :=
  .cons (.assignGlob NGlob.zaehler (.slot NTab.tabA () nI0 (nDarf _ _)) rfl (nGd _ _))
    (.ret .empty List.Perm.nil)

def nRumpfZB : Endblock nD (vertragVon nD NFn.zaehlB) false [] [] :=
  .cons (.assignSlot NTab.tabB () nI0 (.glob NGlob.zaehler (nGd _ _)) rfl (nDarf _ _))
    (.ret .empty List.Perm.nil)

/-- The condition of the leak: `tabA[0] == 0`. -/
def lkC : Expr nD [] [] .bool := .eq (.slot NTab.tabA () nI0 (nDarf _ _)) (.lit 0)

/-- The write under it: `tabB[0] = 1`. -/
def lkW : Stmt nD (vertragVon nD NFn.leck) false [] [] [] :=
  .assignSlot NTab.tabB () nI0 (nW 1 (by decide) (by decide)) rfl (nDarf _ _)

def lkS : Stmt nD (vertragVon nD NFn.leck) false [] [] [] := .ite lkC (.cons lkW .nil) .nil

def lkRet : Endblock nD (vertragVon nD NFn.leck) false [] [] := .ret .empty List.Perm.nil

def nRumpfLeck : Endblock nD (vertragVon nD NFn.leck) false [] [] := .cons lkS lkRet

def nP : Programm nD where
  invariante := fun i => nomatch i
  requires := fun _ => .tru
  ensures := fun _ => .tru
  rumpf
    | .hauptA => nRumpfA
    | .hauptB => nRumpfB
    | .kern => nRumpfKern
    | .ruhe => .ret .empty List.Perm.nil
    | .zaehlA => nRumpfZA
    | .zaehlB => nRumpfZB
    | .leck => nRumpfLeck

def nFs : List nD.Fn := [NFn.hauptA, NFn.hauptB, NFn.kern, NFn.ruhe, NFn.zaehlA, NFn.zaehlB,
  NFn.leck]

theorem nFs_voll : ∀ g : nD.Fn, g ∈ nFs := by
  intro g
  cases g <;> (unfold nFs; repeat (first | exact List.mem_cons_self | apply List.mem_cons_of_mem))

def nCs : List (nD.Tab ⊕ nD.Glob) :=
  [.inl NTab.tabA, .inl NTab.tabB, .inr NGlob.konfig, .inr NGlob.zaehler]

theorem nCs_voll : ∀ c : nD.Tab ⊕ nD.Glob, c ∈ nCs := by
  intro c
  cases c with
  | inl t => cases t <;>
      (unfold nCs; repeat (first | exact List.mem_cons_self | apply List.mem_cons_of_mem))
  | inr g => cases g <;>
      (unfold nCs; repeat (first | exact List.mem_cons_self | apply List.mem_cons_of_mem))

/-! ## 3. Domains, policy, labels, oracle -/
end NIZeuge
end Gabbro.Grammatik
