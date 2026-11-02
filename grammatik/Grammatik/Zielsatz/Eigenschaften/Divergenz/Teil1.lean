module
public import Grammatik.Zielsatz.Eigenschaften.Divergenz.Teil1a

public import Grammatik.Zielsatz.Eigenschaften.NeverAsm
public import Grammatik.Logik.Ruf.Maschine.RufMaschineF
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtGanz
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



namespace Gabbro.Grammatik.Zielsatz

open Gabbro.Grammatik

/-! ## 5. Witness declaration: one table, a writer that diverges, a `-> never` axiom -/

/-- Signature of `schreib`: one `.int 0 10` parameter, no result, holds
    the lock, may write the table. -/
def divSigW : Signatur Unit Empty Unit Empty where
  params := [.int 0 10]
  erg := none
  gruende := 0
  haelt := [()]
  schreibt := fun _ => true
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

/-- Signature of `lies`: no parameters, one `.int 0 100` result, holds the
    lock, writes nothing. -/
def divSigR : Signatur Unit Empty Unit Empty where
  params := []
  erg := some (.int 0 100)
  gruende := 0
  haelt := [()]
  schreibt := fun _ => false
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

/-- The witness declaration: one table `konto` of 2 slots with one
    `.int 0 100` field, guarded by the single lock `m`; `schreib` is
    `true`, `lies` is `false`; and one axiom -- the accepted `asm` shape of
    a `-> never` routine (`aerg = some .never`, writes nothing). -/
def divD : Deklaration where
  Tab := Unit
  decTab := inferInstance
  count := fun _ => 2
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .int 0 100
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
  Fn := Bool
  sig := fun | true => 0 | false => 1
  sigNr := fun | 0 => divSigW | _ => divSigR
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp only [List.not_mem_nil] at h
  Inv := Empty
  traeger := fun e => nomatch e
  invs := []
  Ax := Unit
  aparams := fun _ => []
  aerg := fun _ => some .never
  aschreibt := fun _ _ => false
  agschreibt := fun _ g => nomatch g
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

/-- The two function ids: `schreib` (`true`) and `lies` (`false`). -/
def divSchreib : divD.Fn := show divD.Fn from true

def divLies : divD.Fn := show divD.Fn from false

/-- The axiom IS `-> never`: the accepted `asm` shape. -/
theorem divAx_never : divD.aerg () = some .never := by rfl

/-- End holdings of `schreib`: the lock. -/
theorem divSchreib_ende :
    (vertragVon divD divSchreib).ende = [Res.held (D := divD) ()] := by rfl

/-- The table access is allowed holding the lock. -/
theorem divDarf : darf divD () [Res.held (D := divD) ()] := by
  intro w h
  simp only [divD] at h
  have e : w = Sum.inl () := List.mem_singleton.mp h
  have hh : w ∈ divD.braucht () := h
  rw [e] at hh ⊢
  exact List.mem_singleton.mpr rfl

/-- Parameters of `schreib`, by computation. -/
theorem divSchreib_params : divD.params divSchreib = [.int 0 10] := by rfl

/-- The argument of the witness run: 7 in `.int 0 10`. -/
def divRho7 : Env divD (divD.params divSchreib) :=
  divSchreib_params.symm ▸ (.cons ⟨7, by decide, by decide⟩ .nil :
    Env divD [.int 0 10])

/-- `schreib` holds the lock: start equals end. -/
theorem divSchreib_start : Signatur.anfang divD (divD.signatur divSchreib) =
    [Res.held (D := divD) ()] := by rfl

/-- Same access right at the `schreib` end holdings. -/
theorem divDarfSchreib : darf divD () (vertragVon divD divSchreib).ende := by
  rw [divSchreib_ende]
  exact divDarf

/-- Index `0` into the two-slot table, in the `schreib` context. -/
def divIdx : Expr divD [.int 0 10] [Res.held (D := divD) ()]
    (.index (divD.count ())) :=
  .widen (by decide) (by decide) (.lit 0)

/-- The cap value `100` in range. -/
def divHundert : Expr divD [.int 0 10] [Res.held (D := divD) ()] (.int 0 100) :=
  .widen (by decide) (by decide) (.lit 100)

/-- The `schreib` write: `konto[0] := 100`. -/
def divWriteSt : Stmt divD (vertragVon divD divSchreib) false [.int 0 10]
    (vertragVon divD divSchreib).ende (vertragVon divD divSchreib).ende :=
  .assignSlot () () divIdx divHundert (by decide) divDarfSchreib

/-- The write at the lock holdings. -/
def divWriteStAt : Stmt divD (vertragVon divD divSchreib) false [.int 0 10]
    [Res.held (D := divD) ()] [Res.held (D := divD) ()] :=
  divSchreib_ende ▸ divWriteSt

/-- The accepted diverging loop: `forever () invariant true {}` -- the
    model shape of lane 225's `never-forever` acceptance (un-leavable body,
    named `progress` assumption `()` as the exit evidence). -/
def divSchleife : Stmt divD (vertragVon divD divSchreib) false [.int 0 10]
    [Res.held (D := divD) ()] [Res.held (D := divD) ()] :=
  .forever () .tru .nil

/-- `schreib` body: write the cap, then diverge. The `ret` is unreachable
    but well-typed -- exactly the accepted `-> never`-shaped body. -/
def divRumpfW :
    Endblock divD (vertragVon divD divSchreib) false [.int 0 10]
      [Res.held (D := divD) ()] :=
  .cons divWriteStAt (.cons divSchleife (.ret .empty (by rfl)))

/-- `lies` holds the lock: start equals end. -/
theorem divLies_start : Signatur.anfang divD (divD.signatur divLies) =
    [Res.held (D := divD) ()] := by rfl

/-- Index `0` in the `lies` body context, at the start holdings. -/
def divIdxBodyR : Expr divD [] (Signatur.anfang divD (divD.signatur divLies))
    (.index (divD.count ())) :=
  divLies_start ▸
    (.widen (by decide) (by decide) (.lit 0) :
      Expr divD [] [Res.held (D := divD) ()] (.index (divD.count ())))

/-- `lies` locks the table in its body context. -/
theorem divDarfBodyR :
    darf divD () (Signatur.anfang divD (divD.signatur divLies)) := by
  rw [divLies_start]
  exact divDarf

/-- `lies` body: return `konto[0]`. -/
def divRumpfR :
    Endblock divD (vertragVon divD divLies) false []
      (Signatur.anfang divD (divD.signatur divLies)) :=
  .ret (.val (.slot () () divIdxBodyR divDarfBodyR)) (by rfl)

/-- The program: `schreib` writes then diverges, `lies` reads; every
    contract `true` (nothing is claimed beyond the divergence shapes). -/
def divP : Programm divD where
  invariante := fun i => nomatch i
  requires := fun _ => .tru
  ensures := fun _ => .tru
  rumpf
    | true => divSchreib_start ▸ divRumpfW
    | false => divLies_start ▸ divRumpfR

/-- The witness oracle: the never-axiom keeps the world, answers raw `0`
    (which never fits `never`); no registers, nothing visible. -/
def divO : Orakel divD where
  wirkt := fun _ σ _ => (σ, 0)
  regLies := fun r => nomatch r
  regSchreib := fun r _ => nomatch r
  sichtbar := fun g => nomatch g

/-- The start memory: both slots read `0`. -/
def divSp0 : Speicher divD :=
  ⟨fun _ _ _ => ⟨0, by decide, by decide⟩, fun g => nomatch g⟩

end Gabbro.Grammatik.Zielsatz
