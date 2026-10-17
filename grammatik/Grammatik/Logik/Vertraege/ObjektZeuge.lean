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
import Grammatik.Logik.Vertraege.ObjektWurzel

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
  params := [.ptr 0 true, .index 4, .ptr 0 false, .index 4]
  erg := none
  gruende := 0
  haelt := []
  schreibt := fun t => t == OTab.T
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

/-- `fn sicht(p : ptr<normal, r> T, k : index T) -> index T` -- a re-view at one table. -/
def sigSicht : Signatur OTab Empty Empty Empty where
  params := [.ptr 0 false, .index 4]
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
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp at h
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
  geteilt_bewacht := fun t h => by cases t; simp at h
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun e => nomatch e

def fA : oD.Fn := OFn.aendern
def fS : oD.Fn := OFn.sicht

theorem darfT : darf oD OTab.T [] := by unfold darf; intro w hw; cases hw

def wert5 {Γ : Ctx} : Expr oD Γ [] (oD.typ OTab.T OFeld.x) :=
  Expr.weiter (lo := 5) (hi := 5) (lo' := 0) (hi' := 7) (by decide) (by decide) (.lit 5)

/-- The index variable `k` of `aendern`, at the generated index type of `T`. -/
def varK : Expr oD (oD.params fA) [] (.index (oD.count OTab.T)) := .var (.dort .hier)

/-- `kp->slots[k].x = 5; return;` -/
def rumpfAendern :
    Endblock oD (vertragVon oD fA) false (oD.params fA) (Signatur.anfang oD (oD.signatur fA)) :=
  .cons (.assignDurch (.var .hier) OTab.T rfl OFeld.x varK wert5 rfl darfT)
    (.ret .keine (List.Perm.refl _))

/-- The answer of `sicht`: its index parameter `k`. -/
def antwortSicht : ErgExpr oD (oD.params fS) (Signatur.anfang oD (oD.signatur fS))
    (vertragVon oD fS).erg := .wert (Expr.var (τ := .index 4) (.dort .hier))

/-- `return k;` -/
def rumpfSicht :
    Endblock oD (vertragVon oD fS) false (oD.params fS) (Signatur.anfang oD (oD.signatur fS)) :=
  .ret antwortSicht (List.Perm.refl _)

def oP : Programm oD where
  invariante := fun i => nomatch i
  requires := fun _ => .wahr
  ensures := fun _ => .wahr
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
  | .aendern => [⟨2, 3, OTab.T, true⟩, ⟨0, 1, OTab.T, false⟩]
  | .sicht => [⟨0, 1, OTab.T, false⟩]

/-- **Both bodies keep the object discipline**, with faithful pairs. -/
theorem zeuge_prog : ProgObjOk objs oP := by
  intro f
  cases f with
  | aendern =>
      refine ⟨⟨⟨.dort .hier, rfl, ⟨2, 3, OTab.T, true⟩, by simp [objs], rfl, rfl, rfl⟩, trivial⟩,
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

def σ0 : World oD where
  slots := fun _ _ _ => ⟨0, by decide, by decide⟩
  globs := fun g => nomatch g
  spur := []

def z (n : Int) (h0 : 0 ≤ n) (h3 : n ≤ 3) : Wert oD (.index 4) := ⟨n, h0, h3⟩

/-- An entry environment of `aendern` with `k = a` and `w = b`. -/
def ρA (a b : Int) (ha0 : 0 ≤ a) (ha3 : a ≤ 3) (hb0 : 0 ≤ b) (hb3 : b ≤ 3) :
    Env oD (oD.params fA) :=
  .cons () (.cons (z a ha0 ha3) (.cons () (.cons (z b hb0 hb3) .nil)))

def ρGleich : Env oD (oD.params fA) := ρA 0 0 (by decide) (by decide) (by decide) (by decide)
def ρGetrennt : Env oD (oD.params fA) := ρA 0 1 (by decide) (by decide) (by decide) (by decide)

/-! ## The counter-model: two names of ONE object -/

theorem zeuge_obj_nicht_getrennt : ¬ ObjGetrennt (objs fA) ρGleich :=
  objGetrennt_nicht_bei_einem (w := rwVon (objs fA)) (a := objVon (objs fA) ρGleich)
    ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide) rfl (o := ⟨OTab.T, 0⟩) rfl rfl

/-- **One real run**: it returns, and `T.slots[0].x` -- the object behind the read-only
    `w` -- went from `0` to `5`. -/
theorem zeuge_lauf_gleich :
    ∃ σ', (rufAt oP oO 0 1 fA σ0 ρGleich).welt = some σ' ∧
      (σ'.slots OTab.T 0 OFeld.x).n = 5 ∧ (σ0.slots OTab.T 0 OFeld.x).n = 0 :=
  ⟨_, rfl, rfl, rfl⟩

/-- **Without `ObjGetrennt` the conclusion of `obj_ruf_rahmen` FAILS** -- on a body that keeps
    the object discipline, at its read-only object parameter. -/
theorem ohne_objGetrennt_nur_versprechen :
    ¬ (∀ (σ σ' : World oD), (rufAt oP oO 0 1 fA σ ρGleich).welt = some σ' →
        ∀ fld, σ'.slots OTab.T 0 fld = σ.slots OTab.T 0 fld) := by
  intro h
  obtain ⟨σ', hl, h5, h0⟩ := zeuge_lauf_gleich
  have := h σ0 σ' hl OFeld.x
  rw [this] at h5
  rw [h5] at h0
  cases h0

/-! ## The positive model: two parameters of ONE table, two objects -/

theorem zeuge_objGetrennt : ObjGetrennt (objs fA) ρGetrennt := by
  intro i j hij _
  right
  have h0 : objVon (objs fA) ρGetrennt ⟨0, by decide⟩ = some ⟨OTab.T, 0⟩ := rfl
  have h1 : objVon (objs fA) ρGetrennt ⟨1, by decide⟩ = some ⟨OTab.T, 1⟩ := rfl
  match i, j with
  | ⟨0, _⟩, ⟨0, _⟩ => exact absurd rfl hij
  | ⟨1, _⟩, ⟨1, _⟩ => exact absurd rfl hij
  | ⟨0, _⟩, ⟨1, _⟩ =>
      rw [h0, h1]; intro e; have := congrArg (fun o => o.map Obj.nr) e; simp at this
  | ⟨1, _⟩, ⟨0, _⟩ =>
      rw [h0, h1]; intro e; have := congrArg (fun o => o.map Obj.nr) e; simp at this

/-- **`obj_ruf_rahmen` on the fixture**: every run of `aendern` at `k = 0, w = 1`, at every
    depth and from every world, leaves every field of `T.slots[1]` -- the object of the
    read-only `w`, in the very table the call writes. -/
theorem zeuge_obj_ruf_rahmen (passes fuel : Nat) (σ σ' : World oD)
    (h : (rufAt oP oO passes fuel fA σ ρGetrennt).welt = some σ') :
    ∀ fld, σ'.slots OTab.T 1 fld = σ.slots OTab.T 1 fld :=
  obj_ruf_rahmen oP oO passes fuel oO_treu objs zeuge_prog fA σ ρGetrennt σ' h
    zeuge_objGetrennt ⟨1, by decide⟩ rfl (o := ⟨OTab.T, 1⟩) rfl

/-- **Non-degenerate**: the run really writes -- `T.slots[0]` changes, in the same table as
    the object the frame keeps. -/
theorem zeuge_lauf_getrennt :
    ∃ σ', (rufAt oP oO 0 1 fA σ0 ρGetrennt).welt = some σ' ∧
      (σ'.slots OTab.T 0 OFeld.x).n = 5 ∧ (σ'.slots OTab.T 1 OFeld.x).n = 0 :=
  ⟨_, rfl, rfl, rfl⟩

/-- Slice 2 cannot express it: `aendern`'s two pointer parameters name ONE carrier. -/
theorem zeuge_nicht_paramGetrennt : ¬ ParamGetrennt oD fA :=
  leihe_nicht_getrennt (D := oD) (ps := oD.params fA) ⟨0, by decide⟩ ⟨2, by decide⟩
    (by decide) (n := 0) (rw := true) (rw' := false) rfl rfl rfl (t := OTab.T) rfl

/-- **Strictly finer than slice 2**: object separation where carrier separation fails. -/
theorem zeuge_obj_feiner : ObjGetrennt (objs fA) ρGetrennt ∧ ¬ ParamGetrennt oD fA :=
  ⟨zeuge_objGetrennt, zeuge_nicht_paramGetrennt⟩

/-! ## The borrow rule: a re-view answers the object it was handed -/

/-- `umsicht_behaelt` on `sicht`: every completed call answers its own `k`. -/
theorem zeuge_umsicht (passes n : Nat) (σ : World oD) (ρ : Env oD (oD.params fS)) (σ' : World oD)
    (v : ErgVal oD (oD.erg fS)) (h : rufAt oP oO passes (n + 1) fS σ ρ = .ok σ' v) :
    ergInt (oD.erg fS) v = ρ.unten 0 :=
  umsicht_behaelt oP oO passes n fS antwortSicht (List.Perm.refl _) rfl rfl σ ρ σ' v h

/-- **Non-degenerate**: a real run of `sicht` at `k = 2` answers `2`. -/
theorem zeuge_sicht_lauf :
    ∃ σ' v, rufAt oP oO 0 1 fS σ0 (.cons () (.cons (z 2 (by decide) (by decide)) .nil)) = .ok σ' v ∧
      ergInt (oD.erg fS) v = some 2 :=
  ⟨_, _, rfl, rfl⟩

/-- The answer of `sicht`, as the index it is. -/
def alsIndex (v : ErgVal oD (oD.erg fS)) : Wert oD (.index 4) := v

/-- An entry environment of `aendern` from two index values. -/
def ρAv (k w : Wert oD (.index 4)) : Env oD (oD.params fA) := .cons () (.cons k (.cons () (.cons w .nil)))

/-- **`aendern(k, sicht(k))` is never separated**: whatever `k`, the answer of `sicht` handed
    as `w` names the object of `k`. -/
theorem zeuge_leihe_nicht_getrennt (passes n : Nat) (a : Int) (ha0 : 0 ≤ a) (ha3 : a ≤ 3)
    (σ σ' : World oD) (v : ErgVal oD (oD.erg fS))
    (h : rufAt oP oO passes (n + 1) fS σ (.cons () (.cons (z a ha0 ha3) .nil)) = .ok σ' v) :
    ¬ ObjGetrennt (objs fA) (ρAv (z a ha0 ha3) (alsIndex v)) := by
  have hv := zeuge_umsicht passes n σ _ σ' v h
  have hv' : (alsIndex v).n = a := by
    have e : ergInt (oD.erg fS) v = some (alsIndex v).n := rfl
    rw [e] at hv
    exact Option.some.inj hv
  refine objGetrennt_nicht_bei_einem (w := rwVon (objs fA)) ⟨0, by decide⟩ ⟨1, by decide⟩
    (by decide) rfl (o := ⟨OTab.T, a⟩) rfl ?_
  show Option.map _ (some (alsIndex v).n) = _
  rw [hv']; rfl

/-! ## The bridge on the fixture -/

/-- `aendern(k, sicht(k))`: `k` and its re-view share the root -- `R014` refuses it. -/
theorem zeuge_r014_leihe :
    ¬ R014Rein (rwVon (objs fA)) (fun i => if i.val = 0 then .param 0 else .umsicht (.param 0)) := by
  intro h
  exact h ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide) rfl (.param 0) ⟨rfl, rfl⟩

/-- The provenance of `aendern(k, f)` with `f` a fresh answer. -/
def herkunftFrisch : Fin (objs fA).length → Herkunft :=
  fun i => if i.val = 0 then .param 0 else .frisch 0

/-- `R014` admits it: no common root. -/
theorem zeuge_r014_frisch : R014Rein (rwVon (objs fA)) herkunftFrisch := by
  intro k l hkl _ r ⟨h1, h2⟩
  match k, l with
  | ⟨0, _⟩, ⟨0, _⟩ => exact hkl rfl
  | ⟨1, _⟩, ⟨1, _⟩ => exact hkl rfl
  | ⟨0, _⟩, ⟨1, _⟩ =>
      simp only [herkunftFrisch] at h1 h2; rw [h1] at h2; cases h2
  | ⟨1, _⟩, ⟨0, _⟩ =>
      simp only [herkunftFrisch] at h1 h2; rw [h1] at h2; cases h2

/-- The allocator state of the caller: slots `0` and `1` live, nothing freed. -/
def F0 : ArenaDyn.FreiZustand := ⟨2, [], fun _ h => by cases h⟩

def pNr : Nat → Nat := fun i => if i = 0 then 0 else 1
def wp : Nat → Bool := fun i => i == 0
def pObj : Nat → Obj oD := fun i => ⟨OTab.T, pNr i⟩
def fObj : Nat → Obj oD := fun n => ⟨OTab.T, ArenaDyn.allocStrom F0 n⟩

theorem zeuge_S2 : ParamVerschieden wp pObj := by
  intro i j hij hw e
  have e' : pNr i = pNr j := by
    have := congrArg Obj.nr e; simp only [pObj] at this; exact_mod_cast this
  simp only [wp, Bool.or_eq_true, beq_iff_eq] at hw
  simp only [pNr] at e'
  rcases hw with rfl | rfl
  · rw [if_pos rfl, if_neg (Ne.symm hij)] at e'; cases e'
  · rw [if_neg hij, if_pos rfl] at e'; cases e'

theorem zeuge_frischNeu : FrischNeu pObj fObj :=
  show FrischNeu (fun i => (⟨OTab.T, pNr i⟩ : Obj oD)) (fun n => ⟨OTab.T, ArenaDyn.allocStrom F0 n⟩) from
  frischNeu_aus_arena (D := oD) OTab.T F0 List.nodup_nil pNr
    (fun i => ⟨show pNr i < 2 from by unfold pNr; split <;> decide, by simp [F0]⟩)

/-- **THE BRIDGE, END TO END**: the call `aendern(k, f)` with `k = 0` (the caller's writable
    parameter) and `f = 2` (the first fresh answer of the allocator) is `R014`-clean, the
    four named hypotheses hold, and every run leaves `T.slots[2]` -- the object of the
    read-only `w`, in the table the call writes. -/
theorem zeuge_r014_ruf_rahmen (passes fuel : Nat) (σ σ' : World oD)
    (h : (rufAt oP oO passes fuel fA σ (ρA 0 2 (by decide) (by decide) (by decide) (by decide))).welt =
      some σ') :
    ∀ fld, σ'.slots OTab.T 2 fld = σ.slots OTab.T 2 fld := by
  refine r014_ruf_rahmen oP oO passes fuel oO_treu objs zeuge_prog fA σ _ σ' h herkunftFrisch wp
    pObj fObj zeuge_S2 zeuge_frischNeu ?_ ?_ zeuge_r014_frisch ⟨1, by decide⟩ rfl
    (o := ⟨OTab.T, 2⟩) rfl
  · intro k o ho
    match k with
    | ⟨0, _⟩ =>
        have e : o = ⟨OTab.T, 0⟩ := (Option.some.inj ho).symm
        subst e; rfl
    | ⟨1, _⟩ =>
        have e : o = ⟨OTab.T, 2⟩ := (Option.some.inj ho).symm
        subst e; rfl
  · intro k hk i hi
    match k with
    | ⟨0, _⟩ =>
        simp [herkunftFrisch, Herkunft.wurzeln] at hi
        subst hi; rfl
    | ⟨1, _⟩ => cases hk

/-- Non-degenerate: that run really writes `T.slots[0]`. -/
theorem zeuge_r014_lauf :
    ∃ σ', (rufAt oP oO 0 1 fA σ0 (ρA 0 2 (by decide) (by decide) (by decide) (by decide))).welt =
      some σ' ∧ (σ'.slots OTab.T 0 OFeld.x).n = 5 ∧ (σ'.slots OTab.T 2 OFeld.x).n = 0 :=
  ⟨_, rfl, rfl, rfl⟩

#print axioms Gabbro.Grammatik.ObjektZeuge.zeuge_prog
#print axioms Gabbro.Grammatik.ObjektZeuge.zeuge_obj_nicht_getrennt
#print axioms Gabbro.Grammatik.ObjektZeuge.zeuge_lauf_gleich
#print axioms Gabbro.Grammatik.ObjektZeuge.ohne_objGetrennt_nur_versprechen
#print axioms Gabbro.Grammatik.ObjektZeuge.zeuge_objGetrennt
#print axioms Gabbro.Grammatik.ObjektZeuge.zeuge_obj_ruf_rahmen
#print axioms Gabbro.Grammatik.ObjektZeuge.zeuge_lauf_getrennt
#print axioms Gabbro.Grammatik.ObjektZeuge.zeuge_obj_feiner
#print axioms Gabbro.Grammatik.ObjektZeuge.zeuge_umsicht
#print axioms Gabbro.Grammatik.ObjektZeuge.zeuge_sicht_lauf
#print axioms Gabbro.Grammatik.ObjektZeuge.zeuge_leihe_nicht_getrennt
#print axioms Gabbro.Grammatik.ObjektZeuge.zeuge_r014_leihe
#print axioms Gabbro.Grammatik.ObjektZeuge.zeuge_r014_frisch
#print axioms Gabbro.Grammatik.ObjektZeuge.zeuge_S2
#print axioms Gabbro.Grammatik.ObjektZeuge.zeuge_frischNeu
#print axioms Gabbro.Grammatik.ObjektZeuge.zeuge_r014_ruf_rahmen
#print axioms Gabbro.Grammatik.ObjektZeuge.zeuge_r014_lauf

end ObjektZeuge

end Gabbro.Grammatik
