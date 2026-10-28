/-
  File:      Grammatik/Logik/Vertraege/GetrenntZeuge.lean
  Subject:   The witnesses of `Getrennt.lean` -- one NON-degenerate fixture, both sides.

  THE FIXTURE. Two tables `T` and `U` (two slots each, one field in `0 .. 7`), and two
  functions with the SAME body (store `5` into `T.slots[0].x` through the first,
  writable, pointer parameter) and the same declared frame (`writes T` -- the table of
  the first parameter, so `RahmenUeberParams` holds for both):

    * `aendern (k : ptr rw T, w : ptr r T)` -- the `gift/1444` shape at the model's
      granularity: the read-only parameter names the carrier the writable one writes.
      NOT `ParamGetrennt` (`zeuge_aendern_nicht_getrennt`), and one real `rufAt` run changes
      the carrier of `w` (`zeuge_aendern_lauf`): the per-parameter frame "`w` is only
      read" is FALSE there (`ohne_getrennt_nur_versprechen`).
    * `getrennt (k : ptr rw T, q : ptr r U)` -- `ParamGetrennt` (decided), and
      `getrennt_ruf_rahmen` gives: every run leaves `U` (the carrier of `q`) as it was
      (`getrennt_ruf_rahmen_zeuge`). The run really writes (`zeuge_getrennt_lauf`: `T`
      changes), so the theorem is not about a body that does nothing.

  Read with the header of `Getrennt.lean`: `aendern`'s two parameters are two different
  NAMES (two roots for `R014`), and the model still makes them one carrier -- roots are
  finer than carriers (obstruction 1).
-/
import Grammatik.Logik.Vertraege.Getrennt

namespace Gabbro.Grammatik

namespace GetrenntZeuge

inductive GTab where
  | T
  | U
  deriving DecidableEq

inductive GFeld where
  | x
  deriving DecidableEq

inductive GFn where
  | aendern
  | getrennt
  deriving DecidableEq

/-- `fn aendern(k : ptr<normal, rw> T, w : ptr<normal, r> T) effects { writes k, reads w }`. -/
def sigAendern : Signatur GTab Empty Empty Empty where
  params := [.ptr 0 true, .ptr 0 false]
  erg := none
  gruende := 0
  haelt := []
  schreibt := fun t => t == GTab.T
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

/-- `fn getrennt(k : ptr<normal, rw> T, q : ptr<normal, r> U) effects { writes k, reads q }`. -/
def sigGetrennt : Signatur GTab Empty Empty Empty where
  params := [.ptr 0 true, .ptr 1 false]
  erg := none
  gruende := 0
  haelt := []
  schreibt := fun t => t == GTab.T
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

/-- A re-view at one pointer type: `fn sicht(r : ptr<normal, r> T) -> ptr<normal, r> T`. -/
def sigSicht : Signatur GTab Empty Empty Empty where
  params := [.ptr 0 false]
  erg := some (.ptr 0 false)
  gruende := 0
  haelt := []
  schreibt := fun _ => false
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

abbrev gD : Deklaration where
  Tab := GTab
  decTab := inferInstance
  count := fun _ => 2
  Feld := fun _ => GFeld
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .int 0 7
  erlaubt := fun _ _ _ _ => false
  tabNr := fun | 0 => some GTab.T | 1 => some GTab.U | _ => none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun e => nomatch e
  nutzlast := fun e => nomatch e
  atomar := fun e => nomatch e
  geteilt := fun _ => false
  ggeteilt := fun e => nomatch e
  Lock := Empty
  decLock := inferInstance
  rang := fun L => nomatch L
  maskiert := fun _ => false
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := fun _ => []
  gbraucht := fun e => nomatch e
  eigner := fun _ => []
  Fn := GFn
  sig := fun | .aendern => 0 | .getrennt => 1
  sigNr := fun | 0 => sigAendern | 1 => sigGetrennt | _ => sigAendern
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
  geteilt_bewacht := fun t h => by cases t <;> simp only [Bool.false_eq_true] at h
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun e => nomatch e

def gAendern : gD.Fn := GFn.aendern
def gGetrennt : gD.Fn := GFn.getrennt

theorem darfT : darf gD GTab.T [] := by unfold darf; intro w hw; cases hw

/-- The index `0` into `T` and the value `5`, as expressions of the declared types. -/
def idx0 {Γ : Ctx} : Expr gD Γ [] (.index (gD.count GTab.T)) :=
  Expr.widen (lo := 0) (hi := 0) (lo' := 0) (hi' := gD.count GTab.T - 1)
    (by decide) (by decide) (.lit 0)

def wert5 {Γ : Ctx} : Expr gD Γ [] (gD.typ GTab.T GFeld.x) :=
  Expr.widen (lo := 5) (hi := 5) (lo' := 0) (hi' := 7) (by decide) (by decide) (.lit 5)

/-- Both bodies: `k->slots[0].x = 5; return;` -- a write through the FIRST parameter. -/
def rumpfAendern :
    Endblock gD (vertragVon gD gAendern) false (gD.params gAendern) (Signatur.anfang gD (gD.signatur gAendern)) :=
  .cons (.assignThru (.var .here) GTab.T rfl GFeld.x idx0 wert5 rfl darfT)
    (.ret .empty (List.Perm.refl _))

def rumpfGetrennt :
    Endblock gD (vertragVon gD gGetrennt) false (gD.params gGetrennt) (Signatur.anfang gD (gD.signatur gGetrennt)) :=
  .cons (.assignThru (.var .here) GTab.T rfl GFeld.x idx0 wert5 rfl darfT)
    (.ret .empty (List.Perm.refl _))

def gP : Programm gD where
  invariante := fun i => nomatch i
  requires := fun _ => .tru
  ensures := fun _ => .tru
  rumpf
    | .aendern => rumpfAendern
    | .getrennt => rumpfGetrennt

/-- The hardware: this declaration has no axiom, no register, no global. -/
def gO : Orakel gD where
  wirkt := fun a => nomatch a
  regLies := fun r => nomatch r
  regSchreib := fun r => nomatch r
  sichtbar := fun g => nomatch g

theorem gO_treu : TreuO gO := fun a => nomatch a

/-- The world at the start: every slot at zero. -/
def σ0 : World gD where
  slots := fun _ _ _ => ⟨0, by decide, by decide⟩
  globs := fun g => nomatch g
  spur := []

def ρ2 : Env gD [.ptr 0 true, .ptr 0 false] := .cons () (.cons () .nil)
def ρG : Env gD [.ptr 0 true, .ptr 1 false] := .cons () (.cons () .nil)

/-! ## The converse: without `ParamGetrennt`, the per-parameter frame is only a promise -/

theorem zeuge_aendern_nicht_getrennt : ¬ ParamGetrennt gD gAendern :=
  leihe_nicht_getrennt (D := gD) (ps := gD.params gAendern) ⟨0, by decide⟩ ⟨1, by decide⟩
    (by decide) (n := 0) (rw := true) (rw' := false) rfl rfl rfl (t := GTab.T) rfl

theorem zeuge_aendern_rahmen : RahmenUeberParams gD gAendern := by
  intro t ht
  cases t
  · exact ⟨⟨0, by decide⟩, rfl, rfl⟩
  · exact absurd ht (by decide)

/-- The read-only parameter `w` (position 1) names carrier `T`. -/
theorem zeuge_aendern_w_traeger :
    zaehltFuerTrennung ((gD.params gAendern).get ⟨1, by decide⟩) = false ∧
    traegerVon gD ((gD.params gAendern).get ⟨1, by decide⟩) = some GTab.T := ⟨rfl, rfl⟩

/-- **One real run of `aendern`**: it returns, and `T.slots[0].x` -- the object `w`
    points to -- went from `0` to `5`. -/
theorem zeuge_aendern_lauf :
    ∃ σ', (rufAt gP gO 0 1 gAendern σ0 ρ2).welt = some σ' ∧
      (σ'.slots GTab.T 0 GFeld.x).n = 5 ∧ (σ0.slots GTab.T 0 GFeld.x).n = 0 :=
  ⟨_, rfl, rfl, rfl⟩

/-- **Without `ParamGetrennt` the conclusion of `getrennt_ruf_rahmen` FAILS** -- on a function
    whose frame IS declared over its parameters, at its read-only parameter. -/
theorem ohne_getrennt_nur_versprechen :
    ¬ (∀ (σ : World gD) (ρ : Env gD (gD.params gAendern)) (σ' : World gD),
        (rufAt gP gO 0 1 gAendern σ ρ).welt = some σ' →
        ∀ k (fld : gD.Feld GTab.T), σ'.slots GTab.T k fld = σ.slots GTab.T k fld) := by
  intro h
  obtain ⟨σ', hl, h5, h0⟩ := zeuge_aendern_lauf
  have := h σ0 ρ2 σ' hl 0 GFeld.x
  rw [this] at h5
  rw [h5] at h0
  cases h0

/-! ## The positive side: `ParamGetrennt`, and what it buys -/

theorem zeuge_getrennt : ParamGetrennt gD gGetrennt :=
  paramGetrenntB_wahr gD _ (by decide)

theorem zeuge_getrennt_rahmen : RahmenUeberParams gD gGetrennt := by
  intro t ht
  cases t
  · exact ⟨⟨0, by decide⟩, rfl, rfl⟩
  · exact absurd ht (by decide)

/-- **`getrennt_ruf_rahmen` on the fixture**: every run of `getrennt`, at every depth and
    every world, leaves every slot of `U` -- the carrier of the read-only `q` -- as it was. -/
theorem getrennt_ruf_rahmen_zeuge (passes fuel : Nat) (σ : World gD)
    (ρ : Env gD (gD.params gGetrennt)) (σ' : World gD)
    (h : (rufAt gP gO passes fuel gGetrennt σ ρ).welt = some σ') :
    ∀ k (fld : gD.Feld GTab.U), σ'.slots GTab.U k fld = σ.slots GTab.U k fld :=
  getrennt_ruf_rahmen gP gO passes fuel gO_treu zeuge_getrennt zeuge_getrennt_rahmen
    ⟨1, by decide⟩ rfl (t := GTab.U) rfl σ ρ σ' h

/-- **Non-degenerate**: the run of `getrennt` really writes -- `T` changes -- so the frame
    statement about `U` is about a body that does something. -/
theorem zeuge_getrennt_lauf :
    ∃ σ', (rufAt gP gO 0 1 gGetrennt σ0 ρG).welt = some σ' ∧
      (σ'.slots GTab.T 0 GFeld.x).n = 5 ∧ (σ'.slots GTab.U 0 GFeld.x).n = 0 :=
  ⟨_, rfl, rfl, rfl⟩

/-- `getrennt_schreiben_trennt` on the fixture: a store into `T` (through `k`) leaves the
    slots of `U` (behind `q`). -/
theorem getrennt_schreiben_trennt_zeuge (v : Wert gD (gD.typ GTab.T GFeld.x)) :
    ∀ k' (fb : gD.Feld GTab.U), (σ0.storeSlot GTab.T 0 GFeld.x v).slots GTab.U k' fb =
      σ0.slots GTab.U k' fb :=
  getrennt_schreiben_trennt (D := gD) zeuge_getrennt ⟨0, by decide⟩ ⟨1, by decide⟩
    (by decide) rfl rfl rfl σ0 0 GFeld.x v

/-- The borrow rule on the re-view `sicht : ptr r T -> ptr r T`: its answer has the root
    of its argument, and `aendern(k, sicht(k))` -- in the model, the callee `aendern`
    with its two parameters on that one root -- is the non-`ParamGetrennt` callee above. -/
theorem leihe_wurzel_zeuge :
    ∃ τ, sigSicht.erg = some τ ∧
      traegerVon gD τ = traegerVon gD (sigSicht.params.get ⟨0, by decide⟩) ∧
      traegerVon gD τ = some GTab.T :=
  let ⟨τ, h1, h2⟩ := leihe_wurzel (D := gD) sigSicht ⟨0, by decide⟩ (n := 0) (rw := false)
    (rw' := false) rfl rfl
  ⟨τ, h1, h2, by rw [h2]; rfl⟩

#print axioms Gabbro.Grammatik.GetrenntZeuge.zeuge_aendern_nicht_getrennt
#print axioms Gabbro.Grammatik.GetrenntZeuge.zeuge_aendern_lauf
#print axioms Gabbro.Grammatik.GetrenntZeuge.ohne_getrennt_nur_versprechen
#print axioms Gabbro.Grammatik.GetrenntZeuge.zeuge_getrennt
#print axioms Gabbro.Grammatik.GetrenntZeuge.getrennt_ruf_rahmen_zeuge
#print axioms Gabbro.Grammatik.GetrenntZeuge.zeuge_getrennt_lauf
#print axioms Gabbro.Grammatik.GetrenntZeuge.getrennt_schreiben_trennt_zeuge
#print axioms Gabbro.Grammatik.GetrenntZeuge.leihe_wurzel_zeuge

end GetrenntZeuge

end Gabbro.Grammatik
