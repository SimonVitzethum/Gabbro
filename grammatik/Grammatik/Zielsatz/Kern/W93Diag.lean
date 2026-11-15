-- TEMPORARY diagnostic probe for w93 (deleted before final report).
-- Copies the ak-fixtures of AkzeptiertZeuge (which cannot be imported while that
-- module is red) and evaluates the new VC gate stepwise, compiled (#eval), to
-- locate the kernel-stuck point of ak1_ein_schreiber.
module
public import Grammatik.Logik.Invarianten.Pruefer.Program
public import Grammatik.Logik.Vertraege.Pruefer.Decision
public import Grammatik.Zielsatz.Kern.Akzeptiert
public import Grammatik.Zielsatz.Atomar.AtomarAkzeptiert
public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtSperreZeuge.T1.Teil1Basis
public import Grammatik.Nichtinterferenz.Zeuge.Teil1Basis
public meta import Grammatik.Logik.Invarianten.Pruefer.Program
public meta import Grammatik.Logik.Invarianten.VC.Calls
public meta import Grammatik.Kern.Semantik.Semantik.T1.Teil1
public meta import Grammatik.Logik.Vertraege.Pruefer.Duties
public meta import Grammatik.Logik.Invarianten.VC.Compiler
@[expose] public section

namespace Gabbro.Grammatik.W93Diag

open Invarianten Invarianten.Frag Invarianten.VC Invarianten.Pruefer Vertraege.Pruefer
open Gabbro.Grammatik.NIZeuge

inductive AkFn where
  | a
  | b
  | c
  | ruhe
  deriving DecidableEq

def akSig (w : Bool) (bo : Option Int) : Signatur Unit Empty Unit Empty where
  params := []
  erg := none
  gruende := 0
  haelt := []
  schreibt := fun _ => w
  gschreibt := fun e => (nomatch e)
  konsumiert := []
  produziert := []
  boden := bo

def akSigNr : Nat → Signatur Unit Empty Unit Empty
  | 0 => akSig true none
  | 1 => akSig true none
  | 2 => akSig false (some 1)
  | _ => akSig false none

def akSigOf : AkFn → Nat
  | .a => 0
  | .b => 1
  | .c => 2
  | .ruhe => 3

def akD : Deklaration where
  Tab := Unit
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
  geteilt := fun _ => false
  ggeteilt := fun e => (nomatch e)
  Lock := Unit
  decLock := inferInstance
  rang := fun _ => 0
  maskiert := fun _ => false
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => (nomatch e)
  braucht := fun _ => []
  gbraucht := fun e => (nomatch e)
  eigner := fun _ => []
  Fn := AkFn
  sig := akSigOf
  sigNr := akSigNr
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp only [List.not_mem_nil] at h
  Inv := Empty
  traeger := fun e => (nomatch e)
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
  geteilt_bewacht := fun _ h => by simp only [Bool.false_eq_true] at h
  invarianten_gehalten := fun _ i => (nomatch i)
  ggeteilt_bewacht := fun e => (nomatch e)

instance : DecidableEq akD.Fn := inferInstanceAs (DecidableEq AkFn)
instance : DecidableEq akD.Ax := inferInstanceAs (DecidableEq Empty)

def akA : akD.Fn := AkFn.a
def akB : akD.Fn := AkFn.b
def akC : akD.Fn := AkFn.c
def akRuhe : akD.Fn := AkFn.ruhe

theorem akDarf (Λ : List (Res akD)) : darf akD () Λ := fun _ h => (nomatch h)

def akI0 {Γ : Ctx} {Λ : List (Res akD)} : Expr akD Γ Λ (.index 2) :=
  .widen (by decide) (by decide) (.lit 0)

def ak1 {Γ : Ctx} {Λ : List (Res akD)} : Expr akD Γ Λ (.int 0 100) :=
  .widen (by decide) (by decide) (.lit 1)

def ak2 {Γ : Ctx} {Λ : List (Res akD)} : Expr akD Γ Λ (.int 0 100) :=
  .widen (by decide) (by decide) (.lit 2)

def akT1 {Γ : Ctx} {Λ : List (Res akD)} : Expr akD Γ Λ .bool :=
  .eq (.slot () () akI0 (akDarf Λ)) ak1

def akRumpfA : Endblock akD (vertragVon akD akA) false [] [] :=
  .cons (.assignSlot () () akI0 ak1 rfl (akDarf _)) (.ret .empty List.Perm.nil)

def akRumpfB : Endblock akD (vertragVon akD akB) false [] [] :=
  .cons (.assignSlot () () akI0 ak2 rfl (akDarf _)) (.ret .empty List.Perm.nil)

def akP1 : Programm akD where
  invariante := fun i => (nomatch i)
  requires := fun _ => .tru
  ensures
    | .a => akT1
    | _ => .tru
  rumpf
    | .a => akRumpfA
    | .b => akRumpfB
    | .c => .ret .empty List.Perm.nil
    | .ruhe => .ret .empty List.Perm.nil

def akFs : List akD.Fn := [akA, akB, akC, akRuhe]

def akS : SperrInv akD := SperrInv.leer akD

def diagSources : LockSources akS := fun _ => none

-- stepwise compiled evaluations
#eval ((invariantFormula akP1 ([] : List akD.Inv)).toOption.isSome)
#eval ((translate (akP1.requires akA) (Env.nil : Env akD [])).toOption.isSome)
#eval ((postFormula akP1 akA Env.nil ()).toOption.isSome)
#eval ((checkFunction akP1 akS diagSources {} none akA).toOption.isSome)
#eval ((checkFunction akP1 akS diagSources {} none akB).toOption.isSome)
#eval ((checkFunction akP1 akS diagSources {} none akC).toOption.isSome)
#eval ((checkFunction akP1 akS diagSources {} none akRuhe).toOption.isSome)
#eval (invariantVCB akP1 akS akFs diagSources)

/-- Lock sources for `zS` (mirrors the PoolZeuge fixture edit): constantly-true
    invariant reified by closed `.tru`. -/
def zDiagSources : Invarianten.Pruefer.LockSources zS := fun _ => some
  { resources := []
    expression := .tru
    correct := fun _ => rfl }

def diagZpb : String :=
  match checkInvariantVC zPB zS zFs zDiagSources with
  | .ok _ => "ok"
  | .error e => e.message

#eval diagZpb
#eval (invariantVCB zPB zS zFs zDiagSources)

def diagNp : String :=
  match checkInvariantVC nP (SperrInv.leer nD) nFs (fun _ => none) with
  | .ok _ => "ok"
  | .error e => e.message

#eval diagNp
#eval (invariantVCB nP (SperrInv.leer nD) nFs (fun _ => none))

/-- Full-Bool kernel replicas of the PoolZeuge/Atomar edits (same computation
    the witness theorems decide). -/
example : Akzeptiert zPB zS zFs [()] [.inl ()] [zHaupt, zHaupt] (sources := zDiagSources) = true := by
  decide +kernel

/-- Local replica of `SchwachZeuge.nS` (empty orte, vacuous inv; `S` is
    computationally irrelevant for `nP` since no body uses a lock). -/
def nSprobe : SperrInv nD := ⟨(fun e => nomatch e), (fun e => nomatch e)⟩

def n1wsProbe : List nD.Fn := [NFn.hauptA, NFn.hauptB, NFn.kern]

example : AkzeptiertX nP nSprobe nFs [] nCs n1wsProbe = true := by
  decide +kernel

/-- `hP` replica (copied bodies/contract; atomic `konfig` read with genuinely
    violated `tabB[0] == 1` ensures): the gate must refuse. -/
def hCProbe : Expr nD [] [] .bool :=
  .eq (.glob NGlob.konfig (nGd _ _)) (.slot NTab.tabB () nI0 (nDarf _ _))

def hLiesProbe : Stmt nD (vertragVon nD NFn.zaehlB) false [] [] [] :=
  .assignSlot NTab.tabB () nI0 (.glob NGlob.konfig (nGd _ _)) rfl (nDarf _ _)

def hSetzeProbe (k : Int) (h0 : (0 : Int) ≤ k) (h9 : k ≤ 9) : Stmt nD (vertragVon nD NFn.zaehlB) false [] [] [] :=
  .assignSlot NTab.tabB () nI0 (nW k h0 h9) rfl (nDarf _ _)

def hTestProbe : Stmt nD (vertragVon nD NFn.zaehlB) false [] [] [] :=
  .ite hCProbe (.cons (hSetzeProbe 1 (by decide) (by decide)) .nil) (.cons (hSetzeProbe 2 (by decide) (by decide)) .nil)

def hRumpfProbe : Endblock nD (vertragVon nD NFn.zaehlB) false [] [] :=
  .cons hLiesProbe (.cons hTestProbe (.ret .empty List.Perm.nil))

def hEnsProbe : Expr nD (ErgCtx (nD.params NFn.zaehlB) (nD.erg NFn.zaehlB)) (vertragVon nD NFn.zaehlB).ende
    .bool :=
  .eq (.slot NTab.tabB () nI0 (nDarf _ _)) (nW 1 (by decide) (by decide))

def hPProbe : Programm nD where
  invariante := fun i => (nomatch i)
  requires := fun _ => .tru
  ensures
    | .hauptA => .tru
    | .hauptB => .tru
    | .kern => .tru
    | .ruhe => .tru
    | .zaehlA => .tru
    | .zaehlB => hEnsProbe
    | .leck => .tru
  rumpf
    | .hauptA => nRumpfA
    | .hauptB => nRumpfB
    | .kern => nRumpfKern
    | .ruhe => .ret .empty List.Perm.nil
    | .zaehlA => nRumpfZA
    | .zaehlB => hRumpfProbe
    | .leck => nRumpfLeck

def hwsProbe : List nD.Fn := [NFn.kern, NFn.zaehlB]

example : AkzeptiertX hPProbe nSprobe nFs [] nCs hwsProbe = false := by
  decide +kernel

end Gabbro.Grammatik.W93Diag
