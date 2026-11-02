/-
  File:      Grammatik/Logik/Vertraege/ObjektZeuge.lean
  Subject:   The witnesses of `Objekte.lean`, `ObjektRahmen.lean` and `ObjektWurzel.lean` --
             ONE non-degenerate fixture, both sides, at the case slice 2 could not express.

  THE FIXTURE. One table `T` (four slots, one field `x` in `0 .. 7`) and two functions:

    * `aendern (kp : ptr rw T, k : index T, wp : ptr r T, w : index T)` with the frame
      `writes T` and the body `kp->slots[k].x = 5; return;` -- two object parameters
      of ONE table: `(kp, k)` writable, `(wp, w)` read-only. Slice 2 cannot separate them
      (`zeuge_nicht_paramGetrennt`: one carrier); the object layer can.
    * `sicht (p : ptr r T, k : index T) -> index T` with the body `return k;` -- a re-view
      at one table.

  Both bodies keep the object discipline (`zeuge_prog`). Then:

    * COUNTER-MODEL: at `k = w = 0` the two parameters are ONE object, the frame is not
      `ObjGetrennt` (`zeuge_obj_nicht_getrennt`), and one real run moves the object behind
      the read-only `w` from 0 to 5 (`zeuge_lauf_gleich`): the per-parameter frame fails
      (`ohne_objGetrennt_nur_versprechen`).
    * POSITIVE MODEL: at `k = 0, w = 1` the two parameters of ONE table are two objects
      (`zeuge_objGetrennt`), every run at every depth and world leaves `w`'s object
      (`zeuge_obj_ruf_rahmen`), and the run really writes `k`'s object in the same table
      (`zeuge_lauf_getrennt`). `zeuge_obj_feiner`: object separation without carrier
      separation -- strictly finer than slice 2.
    * BORROW RULE: `sicht` answers the object it was handed (`zeuge_umsicht`, a real run
      `zeuge_sicht_lauf`), so `aendern(k, sicht(k))` is never `ObjGetrennt`
      (`zeuge_leihe_nicht_getrennt`), and its provenance is refused by `R014`
      (`zeuge_r014_leihe`).
    * THE BRIDGE: `aendern(k, frisch)` with a fresh answer of the model's allocator is
      `R014`-clean (`zeuge_r014_frisch`), the four named hypotheses hold for it, and
      `r014_ruf_rahmen` gives the frame for every run (`zeuge_r014_ruf_rahmen`).
-/
module
public import Grammatik.Logik.Vertraege.Objekt.ObjektWurzel
@[expose] public section


namespace Gabbro.Grammatik

namespace ObjektZeuge

inductive OTab where
  | T
  deriving DecidableEq

inductive OFeld where
  | x
  deriving DecidableEq

inductive OFn where
  | aendern
  | sicht
  deriving DecidableEq

/-- `fn aendern(kp : ptr<normal, rw> T, k : index T, wp : ptr<normal, r> T, w : index T)
    effects { writes kp }`. -/
def sigAendern : Signatur OTab Empty Empty Empty where
  params := [.ptr (.table 0 (true, true)), .index 4, .ptr (.table 0 (true, false)), .index 4]
  erg := none
  gruende := 0
  haelt := []
  schreibt := fun t => t == OTab.T
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

/-- `fn sicht(p : ptr<normal, r> T, k : index T) -> index T` -- a re-view at one table. -/
def sigSicht : Signatur OTab Empty Empty Empty where
  params := [.ptr (.table 0 (true, false)), .index 4]
  erg := some (.index 4)
  gruende := 0
  haelt := []
  schreibt := fun _ => false
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

abbrev oD : Deklaration where
  Tab := OTab
  decTab := inferInstance
  count := fun _ => 4
  Feld := fun _ => OFeld
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .int 0 7
  erlaubt := fun _ _ _ _ => false
  tabNr := fun | 0 => some OTab.T | _ => none
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
  Fn := OFn
  sig := fun | .aendern => 0 | .sicht => 1
  sigNr := fun | 0 => sigAendern | 1 => sigSicht | _ => sigAendern
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
  geteilt_bewacht := fun t h => by cases t; simp only [Bool.false_eq_true] at h
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun e => nomatch e

def fA : oD.Fn := OFn.aendern
def fS : oD.Fn := OFn.sicht

theorem darfT : darf oD OTab.T [] := by unfold darf; intro w hw; cases hw

def wert5 {Γ : Ctx} : Expr oD Γ [] (oD.typ OTab.T OFeld.x) :=
  Expr.widen (lo := 5) (hi := 5) (lo' := 0) (hi' := 7) (by decide) (by decide) (.lit 5)

/-- The index variable `k` of `aendern`, at the generated index type of `T`. -/
def varK : Expr oD (oD.params fA) [] (.index (oD.count OTab.T)) := .var (.there .here)

/-- `kp->slots[k].x = 5; return;` -/
def rumpfAendern :
    Endblock oD (vertragVon oD fA) false (oD.params fA) (Signatur.anfang oD (oD.signatur fA)) :=
  .cons (.assignThru (.var .here) OTab.T rfl OFeld.x varK wert5 rfl darfT)
    (.ret .empty (List.Perm.refl _))

/-- The answer of `sicht`: its index parameter `k`. -/
def antwortSicht : ErgExpr oD (oD.params fS) (Signatur.anfang oD (oD.signatur fS))
    (vertragVon oD fS).erg := .val (Expr.var (τ := .index 4) (.there .here))

/-- `return k;` -/
def rumpfSicht :
    Endblock oD (vertragVon oD fS) false (oD.params fS) (Signatur.anfang oD (oD.signatur fS)) :=
  .ret antwortSicht (List.Perm.refl _)

def oP : Programm oD where
  invariante := fun i => nomatch i
  requires := fun _ => .tru
  ensures := fun _ => .tru
  rumpf
    | .aendern => rumpfAendern
    | .sicht => rumpfSicht

def oO : Orakel oD where
  wirkt := fun a => nomatch a
  regLies := fun r => nomatch r
  regSchreib := fun r => nomatch r
  sichtbar := fun g => nomatch g

theorem oO_treu : TreuO oO := fun a => nomatch a

/-- The object parameters: `aendern` has `(kp, k)` writable (index at bottom position 2,
    capability at 3) and `(wp, w)` read-only (0 and 1); `sicht` has `(p, k)` read-only. -/
def objs : oD.Fn → List (ObjPar oD)
  | .aendern => [⟨2, 3, OTab.T, true, true, 0, none⟩, ⟨0, 1, OTab.T, false, true, 0, none⟩]
  | .sicht => [⟨0, 1, OTab.T, false, true, 0, none⟩]

/-- **Both bodies keep the object discipline**, with faithful pairs. -/
theorem zeuge_prog : ProgObjOk objs oP := by
  intro f
  cases f with
  | aendern =>
      refine ⟨⟨⟨.there .here, rfl, ⟨2, 3, OTab.T, true, true, 0, none⟩, by simp only [objs, List.mem_cons, ObjPar.mk.injEq, reduceCtorEq, Nat.reduceEqDiff, Bool.true_eq_false,
  and_false, and_self, List.not_mem_nil, or_self, or_false], rfl, rfl, rfl⟩, trivial⟩,
        ?_, ?_⟩
      · intro op hop hrw
        simp only [objs, List.mem_cons, List.not_mem_nil, or_false] at hop
        rcases hop with rfl | rfl
        · decide
        · cases hrw
      · intro op hop
        simp only [objs, List.mem_cons, List.not_mem_nil, or_false] at hop
        rcases hop with rfl | rfl
        · exact ⟨rfl, 0, rfl, rfl⟩
        · exact ⟨rfl, 0, rfl, rfl⟩
  | sicht =>
      refine ⟨trivial, ?_, ?_⟩
      · intro op hop hrw
        simp only [objs, List.mem_cons, List.not_mem_nil, or_false] at hop
        subst hop; cases hrw
      · intro op hop
        simp only [objs, List.mem_cons, List.not_mem_nil, or_false] at hop
        subst hop
        exact ⟨rfl, 0, rfl, rfl⟩


end ObjektZeuge

end Gabbro.Grammatik
