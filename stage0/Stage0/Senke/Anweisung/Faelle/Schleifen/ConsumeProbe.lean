/- Two live members, removed in index order by the canonical C11 sweep. -/
module
public import Stage0.Senke.Anweisung.Faelle.Schleifen.Consume
public import Stage0.Senke.Anweisung.Satz
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

/-- `edge` is false and the current-state measure counts live members.
    Today's canonical semantics ignores both and visits indices zero, one. -/
def statement (good : Bool) : Stmt D (vertragVon D ()) false [] [] [] :=
  .consumeTraverse () member .fls (invariant good) 2 mass body

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

/-- An independently specified stop function supplies a nonvacuous call
    contract. The tested sweep itself makes no calls. -/
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

def lowered (good : Bool) : Option (List II × Nat) :=
  lowS 1 (fun _ => 2048) layout (functionFrame program ()) post [3] (0, 0) (statement good)
def code (good : Bool) : List II := ((lowered good).getD ([], 0)).1
def top (good : Bool) : Nat := ((lowered good).getD ([], 0)).2

def functionCode : List II := stopC 104 0

/-- Actual emitted instructions, a separate callable stop, frame headers,
    a protected sentinel, and the two live table cells. -/
def memory (good : Bool) : Runner.Mem where
  b a := if a.toNat < 2048 then (((code good).flatMap encII)[a.toNat]?).getD 0
    else if a.toNat < 2048 + 16 * functionCode.length then
      ((functionCode.flatMap encII)[a.toNat - 2048]?).getD 0
    else if a.toNat = 4112 ∨ a.toNat = 8192 ∨ a.toNat = 8200 then 1
    else if a.toNat = 4120 then 77 else 0
  rd _ := true
  wr _ := true

/-- Both branches emit nonempty code within the same concrete frame. -/
theorem lowering_zeuge :
    lowered true = some (code true, top true) ∧
    lowered false = some (code false, top false) ∧
    0 < (code true).length ∧ 0 < (code false).length ∧
    top true + 8 ≤ 64 ∧ top false + 8 ≤ 64 ∧
    16 * (code true).length < 2048 ∧ 16 * (code false).length < 2048 := by
  decide +kernel

/-- A genuine two-round consumption: the measure is 2, 1, 0 and each round
    removes exactly its own member, in ascending index order. -/
theorem two_members_zeuge :
    (alleIndizes (D.count ())).map (fun k => k.n) = [0, 1] ∧
    (eval initial mass initial .nil).n = 2 ∧
    (eval afterFirst mass afterFirst .nil).n = 1 ∧
    (eval afterSecond mass afterSecond .nil).n = 0 ∧
    (afterFirst.slots () 0 ()).n = 0 ∧ (afterFirst.slots () 1 ()).n = 1 ∧
    (afterSecond.slots () 0 ()).n = 0 ∧ (afterSecond.slots () 1 ()).n = 0 ∧
    execStmt oracle 1 calls (statement true) initial .nil = .ok afterSecond .nil := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Both equality lemmas instantiate on the live two-member fixture. -/
theorem consumeTraverse_equalities_zeuge :
    execStmt oracle 1 calls (statement true) initial .nil =
      execStmt oracle 1 calls (.traverse () (invariant true) body :
        Stmt D (vertragVon D ()) false [] [] []) initial .nil ∧
    lowered true = lowS 1 (fun _ => 2048) layout (functionFrame program ()) post [3] (0, 0)
      (.traverse () (invariant true) body : Stmt D (vertragVon D ()) false [] [] []) :=
  ⟨consumeTraverse_exec_eq_traverse oracle 1 calls () member .fls (invariant true) 2 mass body initial .nil,
    consumeTraverse_lowS_eq_traverse 1 (fun _ => 2048) layout (functionFrame program ())
      post [3] (0, 0) () member .fls (invariant true) 2 mass body⟩

/-- The canonical boundary check stops after the first removal. -/
theorem invariant_stop_zeuge [Kern] :
    execStmt oracle 1 calls (statement false) initial .nil = .logik .schleife ∧
    logikCode (D := D) .schleife = 104 := ⟨rfl, rfl⟩

/-- Current semantics runs even with false membership and a constant zero
    measure. This pins the placeholder behavior until the model changes. -/
theorem ignored_selection_zeuge :
    execStmt oracle 1 calls
      (.consumeTraverse () .fls .tru .tru 0 (.lit 0) body :
        Stmt D (vertragVon D ()) false [] [] []) initial .nil = .ok afterSecond .nil ∧
    lowS 1 (fun _ => 2048) layout (functionFrame program ()) post [3] (0, 0)
      (.consumeTraverse () .fls .tru .tru 0 (.lit 0) body :
        Stmt D (vertragVon D ()) false [] [] []) = lowered true := ⟨rfl, rfl⟩

/-- A body with an unsupported scoped return retains its precise refusal. -/
theorem consumeTraverse_refused_zeuge :
    lowS 1 (fun _ => 2048) layout (functionFrame program ()) post [3] (0, 0)
      (.consumeTraverse () member .fls .tru 2 mass
        (.cons (.retScoped .empty { scopes := [], genau := .refl [] }) .nil) :
        Stmt D (vertragVon D ()) false [] [] []) = none := rfl

end Gabbro.Stage0.Senke.ConsumeProbe
