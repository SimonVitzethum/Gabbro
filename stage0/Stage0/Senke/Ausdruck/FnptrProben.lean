/-
  Subject: Non-degenerate function-pointer fixtures, including a global unavailable in the surface front end.
-/
import Stage0.Senke.BildLese

namespace Gabbro.Stage0.Senke.FnptrProben
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
  wirkt a := nomatch a
  regLies r := nomatch r
  regSchreib r := nomatch r
  sichtbar _ _ := true

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

/-- A global pointer is read after each of two distinct runtime stores. -/
theorem global_call_zeuge :
    (match rufAt P O 1 4 2 world .nil with | .ok _ v => v.n | _ => -1) = 22 := by
  decide +kernel

def image : Except String (Bild D) := bild P layout [0, 1, 2] Fin.val (fun f => toString f.val) 2 [] 512

theorem image_nonempty : image.toOption.isSome = true := by decide +kernel

def img : Bild D := image.toOption.get image_nonempty

/-- Retrieving a successful image keeps its construction equation without normalizing the image. -/
theorem image_eq : image = .ok img := by
  have get_ok {α : Type} (e : Except String α) (h : e.toOption.isSome = true) :
      e = .ok (e.toOption.get h) := by
    cases e with
    | error _ => change false = true at h; cases h
    | ok _ => rfl
  exact get_ok image image_nonempty

/-- Both functions have different, nonzero addresses in an accepted image. -/
theorem image_zeuge : image = .ok img ∧ img.A 0 ≠ img.A 1 ∧ img.A 0 ≠ 0 := by
  have h : (image.map fun b => decide (b.A 0 ≠ b.A 1 ∧ b.A 0 ≠ 0)).toOption = some true := by decide +kernel
  rw [image_eq] at h
  exact ⟨image_eq, by simpa [Except.map, Except.toOption] using h⟩

def refLayout : Lay D := { layout 2048 with fa := fun f => 64 + 16 * f.val }

/-- A reference word names the chosen target; neither target is collapsed to a sentinel. -/
theorem fnref_encoding_zeuge :
    Enc refLayout (.fnptr 0) (⟨0, by decide⟩ : Wert D (.fnptr 0)) (BitVec.ofNat 64 64) ∧
    Enc refLayout (.fnptr 0) (⟨1, by decide⟩ : Wert D (.fnptr 0)) (BitVec.ofNat 64 80) := by
  constructor <;> rfl

/-- A concrete instruction and writable frame, disjoint from the code. -/
def refCode : List II := [ci 1 3 64 0]

def refMem : Runner.Mem where
  b a := ((refCode.flatMap encII)[a.toNat]?).getD 0
  rd _ := true
  wr _ := true

theorem refBytes : BytesAt refMem 0 (refCode.flatMap encII) := by
  intro i hi
  refine ⟨rfl, rfl, ?_⟩
  have h16 : i < 16 := by simpa only [flatMap_enc_len, refCode, List.length_singleton] using hi
  simp only [refMem, Nat.zero_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega),
    List.getElem?_eq_getElem hi, Option.getD_some]

theorem refPre [Kern] : PreS refLayout refMem 0 1024 16 3 refCode (Env.nil : Env D []) := by
  refine ⟨by decide, by decide, ⟨by decide, fun _ _ => rfl, fun _ _ => rfl⟩, ?_, ?_, ?_, trivial, wstab_true _ _⟩
  · exact codeAt_bytes refCode 0 (by decide +kernel) refBytes
  · unfold CodeFar; decide +kernel
  · intro _ x; nomatch x

set_option maxHeartbeats 1200000 in
/-- All premises of the function-reference simulation hold jointly on a concrete nonzero target. -/
theorem fnref_ok_zeuge [Kern] :
    lowE refLayout (Expr.fnref (D := D) (Γ := []) (Λ := []) 0 0 (by decide)) 3 = some (refCode, 4) ∧
    PreS refLayout refMem 0 1024 16 3 refCode (Env.nil : Env D []) ∧
    Ok refMem 0 1024 16 3 refCode (Enc refLayout (.fnptr 0) (⟨0, by decide⟩ : Wert D (.fnptr 0))) := by
  refine ⟨rfl, refPre, ?_⟩
  exact fnref_ok (L := refLayout) (Γ := []) (Λ := []) (f := 0) (n := 0) (hf := by decide)
    (d := 3) (top := 4) (K := 16) (c := refCode) (m := refMem) (pc := 0) (fp := 1024)
    (ρ := Env.nil) (W := fun _ => True) world world rfl (by decide) refPre

end Gabbro.Stage0.Senke.FnptrProben
