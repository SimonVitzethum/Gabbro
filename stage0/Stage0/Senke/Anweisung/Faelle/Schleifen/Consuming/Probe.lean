/- Two live members with current-state selection and a falling measure. -/
module
public import Stage0.Senke.Anweisung.Faelle.Schleifen.Consume
public import Stage0.Senke.Anweisung.Satz
public import Stage0.Senke.Images.Bild
@[expose] public section

namespace Gabbro.Stage0.Senke.ConsumeProbe
open Gabbro.Grammatik Runner.IR Runner.Mem
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- One writable two-cell membership column and one parameterless function. -/
def D : Deklaration where
  Tab := Unit
  count _ := 2
  Feld _ := Unit
  typ _ _ := .int 0 1
  erlaubt _ _ _ _ := false
  tabNr _ := some ()
  Glob := Empty
  gtyp g := nomatch g
  nutzlast g := nomatch g
  atomar g := nomatch g
  geteilt _ := false
  ggeteilt g := nomatch g
  Lock := Empty
  rang l := nomatch l
  maskiert l := nomatch l
  Marke := Empty
  stufen m := nomatch m
  braucht _ := []
  gbraucht g := nomatch g
  eigner _ := []
  Fn := Unit
  sig _ := 0
  sigNr _ := {
    params := [], erg := none, gruende := 0, haelt := []
    schreibt := fun _ => true, gschreibt := fun g => nomatch g
    konsumiert := [], produziert := [] }
  eigner_nie_erzeugt _ _ _ _ h := by cases h
  Inv := Empty
  traeger i := nomatch i
  invs := []
  Ax := Empty
  aparams a := nomatch a
  aerg a := nomatch a
  aschreibt a := nomatch a
  agschreibt a := nomatch a
  Reg := Empty
  rtyp r := nomatch r
  rklasse r := nomatch r
  spiegel r := nomatch r
  rzusage r := nomatch r
  Annahme := Unit
  a10 := ()
  geteilt_bewacht _ h := by cases h
  invarianten_gehalten _ i := nomatch i
  ggeteilt_bewacht g := nomatch g

def access : darf D () [] := by intro w h; cases h

def member : Expr D [.index 2] [] .bool :=
  .eq (.slot () () (.var .here) access) (.lit 1)

def mass : Expr D [] [] (.int 0 2) := .count 2 member

def body : Block D (vertragVon D ()) true [.index 2] [] [] :=
  .cons (.assignSlot () () (.var .here)
    (.widen (by decide) (by decide) (.lit 0)) rfl access) .nil

/-- The failing variant checks cell zero at every boundary: it fails after
    the first removal, before visiting cell one. -/
def invariant (good : Bool) : Expr D [] [] .bool :=
  if good then .tru else
    .eq (.slot () () (.widen (by decide) (by decide) (.lit 0)) access) (.lit 1)

/-- An actual edge, predecessor zero to candidate one. -/
def edge : Expr D [.index 2, .index 2] [] .bool :=
  .and (.eq (.var .here) (.lit 0))
    (.eq (.var (.there .here)) (.lit 1))

/-- Membership and measure are reread after the body removes its member. -/
def statement (good : Bool) : Stmt D (vertragVon D ()) false [] [] [] :=
  .consumeTraverse () member edge (invariant good) 2 mass body

def program : Programm D where
  invariante i := nomatch i
  requires _ := .tru
  ensures _ := .tru
  rumpf _ := .cons (statement true) (.ret .empty (.refl []))

def oracle : Orakel D where
  wirkt a := nomatch a
  regLies r := nomatch r
  regSchreib r := nomatch r
  sichtbar _ _ := true

/-- The consuming witness makes no calls. -/
def calls (f : D.Fn) (_ : World D) (_ : Env D (D.params f)) : RufAusgang f :=
  .logik .schleife

def layout : Lay D where
  fa _ := 2048
  col _ _ := 8192
  ga g := nomatch g
  lo := 8192
  hi := 8208
  tor a := nomatch a
  byte _ := none
  sb := 4096
  st := 1024

def initial : World D where
  slots _ _ _ := ⟨1, by decide, by decide⟩
  globs g := nomatch g
  spur := []

def afterFirst : World D := initial.schreibSlot () [] 0 () ⟨0, by decide, by decide⟩
def afterSecond : World D := afterFirst.schreibSlot () [] 1 () ⟨0, by decide, by decide⟩

def post : List II × Nat :=
  (lowPost layout (functionFrame program ()) program ()
    ((functionFrame program ()).internalResult + returnWords (D.erg ()) (D.gruende ()))).getD ([], 0)

/-- Use exactly the reservation computed from the complete source function. -/
def controlReserved : Nat := (functionFrame program ()).bodyReserved

def lowered (good : Bool) : Option (List II × Nat) :=
  lowS 1 (fun _ => 2048) layout (functionFrame program ()) post [3] (0, 0) (statement good)
    (reserved := controlReserved)

/-- Exact represented indices, shared by the selector and the source body. -/
def zero : Wert D (.index 2) := ⟨0, by decide, by decide⟩
def one : Wert D (.index 2) := ⟨1, by decide, by decide⟩

/-- Empty selection must skip this body completely. -/
def absent : Stmt D (vertragVon D ()) false [] [] [] :=
  .consumeTraverse () .fls .tru .tru 0 (.lit 0) body

/-- The first body pass removes its member, but a constant measure still
    violates the canonical strict-decrease condition. -/
def unchanged : Stmt D (vertragVon D ()) false [] [] [] :=
  .consumeTraverse () member edge .tru 0 (.lit 0) body
/-- Normal, empty-membership, nonfalling-measure and invariant-stop images. -/
def variant (kind : Fin 4) : Stmt D (vertragVon D ()) false [] [] [] :=
  match kind.val with
  | 0 => statement true
  | 1 => absent
  | 2 => unchanged
  | _ => statement false

def loweredVariant (kind : Fin 4) : Option (List II × Nat) :=
  lowS 1 (fun _ => 2048) layout (functionFrame program ()) post [3] (0, 0)
    (variant kind) (reserved := controlReserved)
def code (kind : Fin 4) : List II := ((loweredVariant kind).getD ([], 0)).1
def top (kind : Fin 4) : Nat := ((loweredVariant kind).getD ([], 0)).2

def functionCode : List II := stopC 104 0

/-- The statement image is disjoint from the callable stop, frame and cells. -/
def memory (kind : Fin 4) : Runner.Mem where
  b a := if 16384 ≤ a.toNat ∧ a.toNat < 16384 + 16 * (code kind).length then
      (((code kind).flatMap encII)[a.toNat - 16384]?).getD 0
    else if 2048 ≤ a.toNat ∧ a.toNat < 2048 + 16 * functionCode.length then
      ((functionCode.flatMap encII)[a.toNat - 2048]?).getD 0
    else if a.toNat = 4112 ∨ a.toNat = 8192 ∨ a.toNat = 8200 then 1
    else if a.toNat = 4120 then 77 else 0
  rd _ := true
  wr _ := true

/-- Retain the canonical read trace as well as the two final cell values. -/
def finished : World D :=
  match execStmt oracle 1 calls (statement true) initial .nil with
  | .ok σ _ => σ
  | _ => initial

end Gabbro.Stage0.Senke.ConsumeProbe
