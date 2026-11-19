/-
  Subject: The fixture of the Stage-0 satisfiability lemma (stream E4): three functions of one signature and a global
           holding a function of that signature.
-/
module
public import Stage0.Senke.Images.BildLese
@[expose] public section


namespace Gabbro.Stage0.Senke.Erfuellbarkeit
open Gabbro.Grammatik Runner.IR
set_option maxRecDepth 10000

/-- Three functions with one signature and one global holding a function of that signature. -/
def D : Deklaration where
  Tab := Empty
  count t := nomatch t
  Feld _ := Empty
  typ t := nomatch t
  erlaubt t := nomatch t
  tabNr _ := none
  Glob := Unit
  gtyp _ := .fnptr 0
  nutzlast _ := []
  atomar _ := false
  geteilt t := nomatch t
  ggeteilt _ := false
  Lock := Empty
  rang l := nomatch l
  maskiert l := nomatch l
  Marke := Empty
  stufen m := nomatch m
  braucht t := nomatch t
  gbraucht _ := []
  eigner t := nomatch t
  Fn := Fin 3
  sig _ := 0
  sigNr _ := {
    params := []
    erg := some (.int 0 100)
    gruende := 0
    haelt := []
    schreibt := fun t => nomatch t
    gschreibt := fun _ => true
    konsumiert := []
    produziert := [] }
  eigner_nie_erzeugt _ t := nomatch t
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
  geteilt_bewacht t := nomatch t
  invarianten_gehalten _ i := nomatch i
  ggeteilt_bewacht _ h := by cases h

instance (n : Nat) : OfNat D.Fn n := inferInstanceAs (OfNat (Fin 3) n)

def fit (f : D.Fn) : RufPasst D (vertragVon D f) (D.sigNr 0) [] where
  hw t := nomatch t
  hg _ h := h
  hk := ⟨[], List.Perm.nil, List.Sublist.refl []⟩
  hh l := nomatch l

/-- Both targets run: the first result is ignored; the second is bound and returned. -/
def body (f : D.Fn) : Endblock D (vertragVon D f) false [] [] :=
  .cons (.assignGlob () (Expr.fnref (D := D) 0 0 (by decide)) (by intros; rfl) (by intro w h; cases h))
    (.cons (.callInd (Expr.glob (D := D) () (by intro w h; cases h)) .nil (fit f) rfl)
      (.cons (.assignGlob () (Expr.fnref (D := D) 1 0 (by decide)) (by intros; rfl) (by intro w h; cases h))
        (.bindCallInd (Expr.glob (D := D) () (by intro w h; cases h)) .nil rfl (fit f) rfl
          (.ret (.val (.var .here)) List.Perm.nil))))

def P : Programm D where
  invariante i := nomatch i
  requires _ := .tru
  ensures _ := .tru
  rumpf f := if f.val = 2 then body f else
    .ret (.val (if f.val = 0 then .widen (by decide) (by decide) (.lit 21)
      else .widen (by decide) (by decide) (.lit 22))) List.Perm.nil

def O : Orakel D where
  wirktL a := nomatch a
  regLiesL r := nomatch r
  regSchreib r := nomatch r
  sichtbarL _ _ := true

def world : World D where
  slots t := nomatch t
  globs _ := ⟨0, by decide⟩
  spur := []

def layout (b : Nat) : Lay D where
  col t := nomatch t
  ga _ := b
  lo := b
  hi := b + 8
  tor a := nomatch a
  byte t := nomatch t
  sye := b + 8

end Gabbro.Stage0.Senke.Erfuellbarkeit
