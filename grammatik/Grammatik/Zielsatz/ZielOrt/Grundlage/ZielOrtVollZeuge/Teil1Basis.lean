module

public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVoll

@[expose] public section



namespace Gabbro.Grammatik

/-! ## 1. The declaration and the program -/

/-- The three functions. -/
inductive VFn where
  | haupt
  | mid
  | ferr
  deriving DecidableEq

def vSigHaupt : Signatur Unit Empty Unit Empty where
  params := []
  erg := none
  gruende := 0
  haelt := []
  schreibt := fun _ => true
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

def vSigMid : Signatur Unit Empty Unit Empty where
  params := []
  erg := none
  gruende := 0
  haelt := []
  schreibt := fun _ => false
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

def vSigErr : Signatur Unit Empty Unit Empty where
  params := []
  erg := some .bool
  gruende := 1
  haelt := []
  schreibt := fun _ => false
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

/-- One guarded boolean table, one lock, one axiom writing the table, three
    functions. -/
def vD : Deklaration where
  Tab := Unit
  decTab := inferInstance
  count := fun _ => 1
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .bool
  erlaubt := fun _ _ _ _ => false
  tabNr := fun | 0 => some () | _ => none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun e => nomatch e
  nutzlast := fun e => nomatch e
  atomar := fun e => nomatch e
  geteilt := fun _ => true
  ggeteilt := fun e => nomatch e
  Lock := Unit
  decLock := inferInstance
  rang := fun _ => 0
  maskiert := fun _ => false
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := fun _ => [.inl ()]
  gbraucht := fun e => nomatch e
  eigner := fun _ => []
  Fn := VFn
  sig := fun | .haupt => 0 | .mid => 1 | .ferr => 2
  sigNr := fun | 0 => vSigHaupt | 1 => vSigMid | _ => vSigErr
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp only [List.not_mem_nil] at h
  Inv := Empty
  traeger := fun e => nomatch e
  invs := []
  Ax := Unit
  aparams := fun _ => []
  aerg := fun _ => none
  aschreibt := fun _ _ => true
  agschreibt := fun _ e => nomatch e
  Reg := Empty
  rtyp := fun e => nomatch e
  rklasse := fun e => nomatch e
  spiegel := fun e => nomatch e
  rzusage := fun e => nomatch e
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun t _ => by decide
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun e => nomatch e

def vHaupt : vD.Fn := VFn.haupt
def vMid : vD.Fn := VFn.mid
def vErr : vD.Fn := VFn.ferr

/-- The lock holdings inside the `locks` block. -/
abbrev vL : List (Res vD) := [Res.held (D := vD) ()]

theorem vDarf : darf vD () vL := by
  intro w h
  have e : w = Sum.inl () := List.mem_singleton.mp h
  subst e
  exact List.mem_singleton.mpr rfl

/-- A call between lock-free functions. -/
theorem vHp (caller callee : vD.Fn) (hw : ∀ t, (vD.signatur callee).schreibt t = true →
    (vertragVon vD caller).schreibt t = true)
    (hh : (vD.signatur callee).haelt = []) (hk : (vD.signatur callee).konsumiert = []) :
    RufPasst vD (vertragVon vD caller) (vD.signatur callee) [] where
  hw := hw
  hg := fun g => nomatch g
  hb := fun c hc => by revert hc; cases caller <;> intro hc <;> cases hc
  hk := by
    unfold Signatur.inputMarks
    rw [hk, OwnerFlow.empty_of_empty (vD.signatur callee).owner]
    exact ⟨[], List.Perm.refl [], by simp only [List.Sublist.refl]⟩
  hh := RufPasst.hh_von (by
    intro L
    rw [hh]
    exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩)
  hx := RufPasst.hx_von (by
    intro L
    rw [hh]
    exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩)

theorem vHpErr : RufPasst vD (vertragVon vD vMid) (vD.signatur vErr) [] :=
  vHp vMid vErr (fun t h => by cases t; exact absurd h (by decide)) rfl rfl

theorem vHpMid : RufPasst vD (vertragVon vD vHaupt) (vD.signatur vMid) [] :=
  vHp vHaupt vMid (fun t h => by cases t; exact absurd h (by decide)) rfl rfl

/-- The one reason of `ferr`. -/
def vR0 : Fin (vertragVon vD vErr).gruende := ⟨0, by decide⟩

/-- `ferr`: the reason return. -/
def vRumpfErr : Endblock vD (vertragVon vD vErr) false [] [] :=
  .retWhy vR0 List.Perm.nil

/-- The `else` block of `mid`: `return`. -/
def vErrBlock : Endblock vD (vertragVon vD vMid) false (.why (vD.gruende vErr) :: [])
    (nach vD vErr []) :=
  .ret .empty List.Perm.nil

/-- `let x = ferr() else r => { return }` -/
def vLetElse : Block vD (vertragVon vD vMid) false [] [] [] :=
  .bindCallElse vErr .nil rfl vHpErr (by decide) vErrBlock .nil

/-- `if true { let x = ferr() else … }` -/
def vIte : Stmt vD (vertragVon vD vMid) false [] [] [] := .ite .tru vLetElse .nil

/-- `mid`: `if true { let x = ferr() else r => { return } }; return`. -/
def vRumpfMid : Endblock vD (vertragVon vD vMid) false [] [] :=
  .cons vIte (.ret .empty List.Perm.nil)

/-- The loop body: `leave`. -/
def vLeave : Block vD (vertragVon vD vHaupt) true [] [] [] := .cons (.leave rfl) .nil

/-- `retry 1 until false { leave } on_exceeded { }` -/
def vRetry : Stmt vD (vertragVon vD vHaupt) false [] [] [] := .retry 1 .fls vLeave .nil

/-- The axiom call `ax()`, under the lock. -/
def vAx : Stmt vD (vertragVon vD vHaupt) false [] vL vL :=
  .axiomCall () .nil rfl (fun _ _ => rfl) (fun e => nomatch e) (fun _ _ => vDarf)
    (fun e => nomatch e)

/-- `locks L { ax() }` -/
def vLocks : Stmt vD (vertragVon vD vHaupt) false [] [] [] :=
  .locks () (fun _ h => nomatch h) (.cons vAx .nil)

/-- `haupt` after its call. -/
def vRestHaupt : Endblock vD (vertragVon vD vHaupt) false [] (nach vD vMid []) :=
  .cons vRetry (.cons vLocks (.ret .empty List.Perm.nil))

/-- The pointer `&mid`. -/
def vZeigerMid {Γ : Ctx} {Λ : List (Res vD)} : Expr vD Γ Λ (.fnptr 1) := .fnref vMid 1 rfl

/-- `(&mid)()` -- an indirect call. -/
def vRufMid : Stmt vD (vertragVon vD vHaupt) false [] [] (nach vD vMid []) :=
  .callInd vZeigerMid .nil vHpMid rfl

/-- `haupt`: `(&mid)(); retry …; locks L { ax() }; return`. -/
def vRumpfHaupt : Endblock vD (vertragVon vD vHaupt) false [] [] :=
  .cons vRufMid vRestHaupt

/-- The witness program: all contracts `true`. -/
def vP : Programm vD where
  invariante := fun i => nomatch i
  requires := fun _ => .tru
  ensures := fun _ => .tru
  rumpf
    | .haupt => vRumpfHaupt
    | .mid => vRumpfMid
    | .ferr => vRumpfErr

def vFs : List vD.Fn := [vHaupt, vMid, vErr]

theorem vFs_voll : ∀ g : vD.Fn, g ∈ vFs := by
  intro g
  cases g
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

theorem vP_fragment : programmImFragmentV vP vFs = true := by decide

/-- The program is NOT in the old fragment: it uses the loop, the exit, the
    error channel and the axiom. -/
theorem vP_nicht_alt : programmImFragment vP vFs = false := by decide

theorem vP_fuss : fussOrtB vP vFs = true := by decide

end Gabbro.Grammatik
