/-
  Scoped-return witnesses: a value return from inside two nested lock scopes
  releases both scopes innermost first and returns the value; a reason return
  through one scope releases it. The release order is the exact
  `World.gibt_foldl_spur` instance (last release on top).
-/
module
public import Stage0.Senke.Anweisung
public import Stage0.Senke.Rueckkehr.EpilogueCode
public import Stage0.Senke.Ausdruck.Aggregat.Layout
public import Stage0.Senke.Funktion
public import Grammatik.Kern.Semantik.Semantik
@[expose] public section


namespace Gabbro.Stage0.Senke.ScopedZeuge

open Gabbro.Grammatik Runner.IR

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- One parameterless function with a bounded integer result and two locks. -/
def D : Deklaration where
  Tab := Empty
  count t := nomatch t
  Feld t := nomatch t
  decFeld t := nomatch t
  typ t _ := nomatch t
  erlaubt _ _ _ _ := false
  tabNr _ := none
  Glob := Empty
  gtyp g := nomatch g
  nutzlast g := nomatch g
  atomar g := nomatch g
  geteilt _ := false
  ggeteilt g := nomatch g
  Lock := Fin 2
  rang l := (l.val : Int)
  maskiert _ := false
  Marke := Empty
  stufen m := nomatch m
  braucht _ := []
  gbraucht g := nomatch g
  eigner _ := []
  Fn := Unit
  sig _ := 0
  sigNr _ := {
    params := [], erg := some (.int 0 100), gruende := 1, haelt := []
    schreibt := fun t => nomatch t
    gschreibt := fun g => nomatch g
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

/-- The inner scope is released first, the outer scope last (on top). -/
def inner : D.Lock := ⟨1, by decide⟩
def outer : D.Lock := ⟨0, by decide⟩

abbrev entry : D.Fn := ()
abbrev V := vertragVon D entry

def heldBoth : List (Res D) := [Res.held inner, Res.held outer]
def heldOne : List (Res D) := [Res.held inner]

def cleanup : RueckRessourcen D V heldBoth :=
  { scopes := [inner, outer], genau := by decide }
def cleanupWhy : RueckRessourcen D V heldOne :=
  { scopes := [inner], genau := by decide }

def result : ErgExpr D [] heldBoth V.erg :=
  .val (.widen (by decide) (by decide) (.lit 7))

def stmt : Stmt D V false [] heldBoth heldBoth := .retScoped result cleanup
def stmtWhy : Stmt D V false [] heldOne heldOne :=
  .retWhyScoped ⟨0, by decide⟩ cleanupWhy
def endStmt : Endblock D V false [] heldBoth := .retScoped result cleanup
def endStmtWhy : Endblock D V false [] heldOne :=
  .retWhyScoped ⟨0, by decide⟩ cleanupWhy

def world : World D where
  slots t := nomatch t
  globs g := nomatch g
  spur := []

def oracle : Orakel D where
  wirkt a := nomatch a
  regLies r := nomatch r
  regSchreib r _ := nomatch r
  sichtbar _ _ := true

def calls (f : D.Fn) (_ : World D) (_ : Env D (D.params f)) : RufAusgang f :=
  .logik .schleife

def released : World D :=
  { world with spur := [Ereignis.gibt outer, Ereignis.gibt inner] }
def releasedWhy : World D :=
  { world with spur := [Ereignis.gibt inner] }

def lay : Lay D where
  col t := nomatch t
  ga g := nomatch g
  lo := 8192
  hi := 8208
  tor a := nomatch a
  byte t := nomatch t
  sb := 4096
  st := 1024

def program : Programm D where
  invariante i := nomatch i
  requires _ := .tru
  ensures _ := .tru
  rumpf _ := (.retWhy ⟨0, by decide⟩ (.refl []) :
    Endblock D (vertragVon D ()) false [] [])

def post : List II × Nat :=
  (lowPost lay (functionFrame program entry) program entry
    ((functionFrame program entry).internalResult +
      returnWords (D.erg entry) (D.gruende entry))).getD ([], 0)

/-- The two-scope return releases both scopes, innermost first, and returns 7. -/
theorem scoped_sem_zeuge :
    execStmt oracle 1 calls stmt world .nil =
      .zurueck released ⟨7, by decide, by decide⟩ := rfl

/-- The trace order is the exact release-fold instance: the last release on top. -/
theorem scoped_spur_zeuge :
    ([inner, outer].foldl World.gibt world).spur =
      [Ereignis.gibt outer, Ereignis.gibt inner] ++ world.spur :=
  World.gibt_foldl_spur world [inner, outer]

/-- The two-scope return lowers to nonempty code. -/
theorem scoped_lowS_zeuge :
    ∃ code top, lowS 1 (fun _ => 0) lay (functionFrame program entry) post
      [] (0, 0) stmt = some (code, top) ∧ 0 < code.length := by
  exact ⟨_, _, rfl, by decide⟩

/-- The reason return through one scope releases exactly that scope. -/
theorem scoped_why_sem_zeuge :
    execStmt oracle 1 calls stmtWhy world .nil =
      .why releasedWhy ⟨0, by decide⟩ := rfl

/-- The one-scope trace is the exact release-fold instance. -/
theorem scoped_why_spur_zeuge :
    ([inner].foldl World.gibt world).spur =
      [Ereignis.gibt inner] ++ world.spur :=
  World.gibt_foldl_spur world [inner]

/-- The reason return through one scope lowers to nonempty code. -/
theorem scoped_why_lowS_zeuge :
    ∃ code top, lowS 1 (fun _ => 0) lay (functionFrame program entry) post
      [] (0, 0) stmtWhy = some (code, top) ∧ 0 < code.length := by
  exact ⟨_, _, rfl, by decide⟩

/-- Both end-block forms lower. -/
theorem scoped_end_lowS_zeuge :
    (lowEnd 1 (fun _ => 0) lay (functionFrame program entry) post
      [] (0, 0) endStmt).isSome = true ∧
    (lowEnd 1 (fun _ => 0) lay (functionFrame program entry) post
      [] (0, 0) endStmtWhy).isSome = true := ⟨rfl, rfl⟩

end Gabbro.Stage0.Senke.ScopedZeuge
