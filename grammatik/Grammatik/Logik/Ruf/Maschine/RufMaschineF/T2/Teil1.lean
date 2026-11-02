module
public import Grammatik.Logik.Ruf.Maschine.RufMaschineF.T2.Teil1Basis
import all Grammatik.Logik.Ruf.Maschine.RufMaschineF.T2.Teil1Basis

public import Grammatik.Logik.Ruf.Maschine.RufMaschineF.T1

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 8. Non-trivial witness: one table, a writing leaf, call and return -/

/-- The witness declaration: one table `Unit` with one field of type
    `.int 0 5` (written by the leaf), one function id (`Bool`), no locks,
    no globals, no axioms. The table gives the run a real memory write:
    `assignSlot` changes slots by construction of `execStmt`. -/
def rufDF : Deklaration where
  Tab := Unit
  decTab := inferInstance
  count := fun _ => 2
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .int 0 5
  erlaubt := fun _ _ _ _ => false
  tabNr := fun | 0 => some () | _ => none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun e => nomatch e
  nutzlast := fun e => nomatch e
  atomar := fun e => nomatch e
  geteilt := fun _ => false
  ggeteilt := fun e => nomatch e
  Lock := Empty
  decLock := inferInstance
  rang := fun e => nomatch e
  maskiert := fun e => nomatch e
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := fun _ => []
  gbraucht := fun e => nomatch e
  eigner := fun _ => []
  Fn := Bool
  sig := fun | true => 0 | false => 1
  sigNr := fun _ =>
    { params := [.int 0 5]
      erg := some (.int 0 6)
      gruende := 0
      haelt := []
      schreibt := fun _ => true
      gschreibt := fun e => nomatch e
      konsumiert := []
      produziert := [] }
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
  geteilt_bewacht := fun t h => by simp only [Bool.false_eq_true] at h
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun e => nomatch e

/-- The witness function id: `false` is the CALLER (its body calls
    `true`); `true` is the CALLEE (the writing body). -/
def rufCallerF : rufDF.Fn := show rufDF.Fn from false

def rufIncF : rufDF.Fn := show rufDF.Fn from true

/-- The `erg` of each function, by computation (case on the id). -/
theorem rufDF_erg (f : rufDF.Fn) :
    rufDF.erg f = some (.int 0 6) := by
  cases f with
  | true => rfl
  | false => rfl

/-- The `params` of each function, by computation (case on the id). -/
theorem rufDF_params (f : rufDF.Fn) :
    rufDF.params f = [.int 0 5] := by
  cases f with
  | true => rfl
  | false => rfl

/-- The single parameter environment: the value 2 in `.int 0 5`. -/
def rufRhoF : Env rufDF (rufDF.params rufIncF) :=
  (rufDF_params rufIncF).symm ▸ (.cons ⟨2, by decide, by decide⟩ .nil :
    Env rufDF [.int 0 5])

/-- The single result value: 3 in `.int 0 6`. -/
def rufVF : ErgVal rufDF (rufDF.erg rufIncF) :=
  (rufDF_erg rufIncF).symm ▸ (⟨3, by decide, by decide⟩ : ErgVal rufDF (some (.int 0 6)))

/-- The callee body: one writing leaf (`assignSlot` to slot 0, the
    parameter value), then `ret` of the parameter. The leaf is a `Stmt`
    under the callee contract with `hw : schreibt = true` (the signature
    writes) and `hL : darf` (no guards needed, `braucht = []`). -/
def rufRumpfF : Endblock rufDF (vertragVon rufDF rufIncF) false
    (rufDF.params rufIncF)
    (Signatur.anfang rufDF (rufDF.signatur rufIncF)) :=
  .cons (.assignSlot () ()
    (.widen (by decide) (by decide) (.lit 0) :
      Expr rufDF (rufDF.params rufIncF)
        (Signatur.anfang rufDF (rufDF.signatur rufIncF)) (.index (rufDF.count ())))
    ((.widen (by decide) (by decide) (.var .here) :
      Expr rufDF (rufDF.params rufIncF)
        (Signatur.anfang rufDF (rufDF.signatur rufIncF)) (.int 0 5))) rfl (fun w => nomatch w))
    (.ret (.val ((.widen (by decide) (by decide) (.var .here) :
      Expr rufDF (rufDF.params rufIncF)
        (Signatur.anfang rufDF (rufDF.signatur rufIncF)) (.int 0 6)))) (by decide))

/-- The call fits: callee writes nothing beyond the caller's rights (both
    write the one table), consumes nothing, holds nothing. -/
theorem rufHpF : RufPasst rufDF (vertragVon rufDF rufCallerF)
    (rufDF.signatur rufIncF) ([] : List (Res rufDF)) where
  hw := fun _ _ => rfl
  hg := fun g => nomatch g
  hk := ⟨[], List.Perm.refl [], List.Sublist.slnil⟩
  hh := fun L => nomatch L

/-- The call arguments: the single parameter variable. -/
def rufArgsF : Args rufDF [Ty.int 0 5] [] (rufDF.params rufIncF) :=
  (rufDF_params rufCallerF).symm ▸ Args.cons (.var .here) Args.nil

/-- The caller body: a single `call` to the callee, returning to the empty
    end. Note the caller contract is `vertragVon rufDF rufCallerF` (same
    signature shape, so `params` coincide by `rufDF_params`). -/
def rufCallerRumpfF : Endblock rufDF (vertragVon rufDF rufCallerF) false
    (rufDF.params rufCallerF)
    (Signatur.anfang rufDF (rufDF.signatur rufCallerF)) :=
  (rufDF_params rufCallerF).symm ▸
    (.cons (.call rufIncF rufArgsF rufHpF rfl)
      (.ret (.val ((.widen (by decide) (by decide) (.var .here) :
        Expr rufDF (rufDF.params rufIncF) [] (.int 0 6)))) (by decide)) :
      Endblock rufDF (vertragVon rufDF rufCallerF) false
        (rufDF.params rufIncF) (nach rufDF rufIncF []))

/-- The program: the caller calls, the callee writes; contracts trivial
    (`wahr`). `requires`/`ensures` play no role in the witness -- only the
    memory move and the log events matter. -/
def rufPF : Programm rufDF where
  invariante := fun i => nomatch i
  requires := fun _ => .tru
  ensures := fun _ => .tru
  rumpf
    | true => rufRumpfF
    | false => rufCallerRumpfF

/-- The witness oracle: no axioms, no registers, nothing visible. -/
def rufOF : Orakel rufDF where
  wirkt := fun a => nomatch a
  regLies := fun r => nomatch r
  regSchreib := fun r => nomatch r
  sichtbar := fun g => nomatch g

/-- The empty world over the witness declaration. -/
def rufWeltF : World rufDF :=
  ⟨fun _ _ _ => ⟨0, by decide, by decide⟩, fun g => Empty.elim g, []⟩

/-- Named pieces of the witness body: the writing leaf and the `ret`
    tail, so the `blatt` step can name them. -/
def leafSF : Stmt rufDF (vertragVon rufDF rufIncF) false (rufDF.params rufIncF)
    (Signatur.anfang rufDF (rufDF.signatur rufIncF))
    (Signatur.anfang rufDF (rufDF.signatur rufIncF)) :=
  .assignSlot () ()
    (.widen (by decide) (by decide) (.lit 0) :
      Expr rufDF (rufDF.params rufIncF)
        (Signatur.anfang rufDF (rufDF.signatur rufIncF)) (.index (rufDF.count ())))
    ((.widen (by decide) (by decide) (.var .here) :
      Expr rufDF (rufDF.params rufIncF)
        (Signatur.anfang rufDF (rufDF.signatur rufIncF)) (.int 0 5))) rfl (fun w => nomatch w)

def restF : Endblock rufDF (vertragVon rufDF rufIncF) false (rufDF.params rufIncF)
    (Signatur.anfang rufDF (rufDF.signatur rufIncF)) :=
  (.ret (.val ((.widen (by decide) (by decide) (.var .here) :
      Expr rufDF (rufDF.params rufIncF)
        (Signatur.anfang rufDF (rufDF.signatur rufIncF)) (.int 0 6)))) (by decide))

theorem rufRumpfF_eq : rufRumpfF = Endblock.cons leafSF restF := by rfl

/-- The leaf is a leaf. -/
theorem leafSF_blatt : leafSF.istBlatt = true := by rfl

end Gabbro.Grammatik
