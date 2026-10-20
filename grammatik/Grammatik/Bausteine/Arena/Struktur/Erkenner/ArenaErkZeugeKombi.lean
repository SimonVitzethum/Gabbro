/-
  File:      Grammatik/ArenaErkZeugeKombi.lean
  Subject:   THE RECOGNIZER ON A REAL ARENA THAT CARRIES A LIST AND A TREE (PLAN-DYNAMIC.md section 8a.1, third pass).

  The arena of `ArenaDynZeuge.lean` shares its link field and its head word between the list and the tree, so it cannot
  carry both. This file declares a second concrete arena with five fields (payload, free link, LIST link, LEFT child,
  RIGHT child) and five words (counter, committed word, free head, LIST head, tree ROOT), four slots, and the world `wk`:
  slot `1` on the free list, the list `2`, the tree `0 (right 3)`, every live slot in at most one structure.

  Accepted (witnesses, run from the real world `wk`):
    * `kombiHang`        -- take slot `1` off the free list, read the root `0`, hang the slot at its (empty) left place,
                            read the list head: the tree is `0 (left 1, right 3)`, the list is untouched;
    * `kombiVersetzen`   -- read the root `0`, cut its leaf child `3` off the tree, link it in at the head of the list:
                            the slot MOVES from the tree to the list (it was in neither in between): tree `0`, list `3 -> 2`.
  Rejected (planted defect, specific to the combination):
    * `doppelGlied`      -- the root, a tree member, is linked into the list: each structure is still well formed, but
                            the slot is in both -- the arena invariant (`Dekl.Ok`) has the disjointness of the two.
-/
import Grammatik.Bausteine.Arena.Struktur.Erkenner.ArenaErkennerZeuge

namespace Gabbro.Grammatik

open Gabbro.Grammatik.ArenaDyn Gabbro.Grammatik.ArenaKette

namespace ErkKombi

/-- Five fields, five words, four slots: payload `0`, free link `1`, list link `2`, left `3`, right `4`; counter `0`,
    committed word `1`, free head `2`, list head `3`, tree root `4`. -/
@[reducible] def FD2 : Deklaration where
  Tab := Unit
  decTab := inferInstance
  count := fun _ => 4
  Feld := fun _ => Fin 5
  decFeld := fun _ => inferInstance
  typ := fun _ f => if f = 0 then .int 0 255 else .int 0 4
  erlaubt := fun _ _ _ _ => false
  tabNr := fun | 0 => some () | _ => none
  Glob := Fin 5
  decGlob := inferInstance
  gtyp := fun _ => .int 0 4
  nutzlast := fun _ => []
  atomar := fun _ => false
  geteilt := fun _ => false
  ggeteilt := fun _ => false
  Lock := Empty
  decLock := inferInstance
  rang := fun e => nomatch e
  maskiert := fun e => nomatch e
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := fun _ => []
  gbraucht := fun _ => []
  eigner := fun _ => []
  Fn := Unit
  sig := fun _ => 0
  sigNr := fun _ =>
    { params := []
      erg := none
      gruende := 0
      haelt := []
      schreibt := fun _ => true
      gschreibt := fun _ => true
      konsumiert := []
      produziert := [] }
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
  geteilt_bewacht := fun t h => by simp at h
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun g h => by simp at h

def FA2 : FreiForm FD2 where
  tab := ()
  feld := 0
  zaehl := 0
  hz := rfl
  hpos := by decide
  komm := 1
  hk := rfl
  hzwei := by decide
  kopf := 2
  hkopf := rfl
  nxt := 1
  hnxt := rfl
  hk1 := by decide
  hk2 := by decide
  hf := by decide

/-- The list link (field `2`) and the list head (word `3`). -/
def LL2 : LinkFeld FA2 where
  f := 2
  hf := rfl
  h1 := by decide
  h2 := by decide

def LG2 : LinkKopf FA2 where
  g := 3
  hg := rfl
  h1 := by decide
  h2 := by decide
  h3 := by decide

/-- The tree: left child (field `3`), right child (field `4`), root (word `4`). -/
def Lf2 : LinkFeld FA2 where
  f := 3
  hf := rfl
  h1 := by decide
  h2 := by decide

def Rf2 : LinkFeld FA2 where
  f := 4
  hf := rfl
  h1 := by decide
  h2 := by decide

def Wz2 : LinkKopf FA2 where
  g := 4
  hg := rfl
  h1 := by decide
  h2 := by decide
  h3 := by decide

/-- **The arena carries a list AND a tree, on different words.** -/
def K2 : Dekl FA2 where
  liste := some ⟨LL2, LG2⟩
  baum := some ⟨Lf2, Rf2, Wz2, by decide⟩
  getrennt := fun l b hl hb => by
    cases hl
    cases hb
    exact ⟨by decide, by decide, by decide⟩

/-- A world from the counter, the free head, the list head, the tree root, the free links, the list links, the left and
    the right links. -/
def wd2 (st kopf lh tr : Int) (nx ln lf rf : Int → Int) : World FD2 where
  slots := fun _ k f =>
    if h0 : f = 0 then (by subst h0; exact (⟨0, by decide, by decide⟩ : Zahl 0 255))
    else if h1 : f = 1 then (by
      have : FD2.typ () f = .int 0 4 := by simp [h0]
      rw [this]; exact InvDynZeuge.zc (nx k))
    else if h2 : f = 2 then (by
      have : FD2.typ () f = .int 0 4 := by simp [h0]
      rw [this]; exact InvDynZeuge.zc (ln k))
    else if h3 : f = 3 then (by
      have : FD2.typ () f = .int 0 4 := by simp [h0]
      rw [this]; exact InvDynZeuge.zc (lf k))
    else (by
      have : FD2.typ () f = .int 0 4 := by simp [h0]
      rw [this]; exact InvDynZeuge.zc (rf k))
  globs := fun g =>
    if g = 0 then InvDynZeuge.zc st else if g = 1 then InvDynZeuge.zc st else if g = 2 then InvDynZeuge.zc kopf
    else if g = 3 then InvDynZeuge.zc lh else InvDynZeuge.zc tr
  spur := []

def nilF : Int → Int := fun _ => 4
/-- The right child of `0` is `3`. -/
def rf0 : Int → Int := fun k => if k = 0 then 3 else 4

/-- Slot `1` on the free list; the list is `2`; the tree is `0` with the right child `3`. -/
def wk : World FD2 := wd2 4 1 2 0 nilF nilF nilF rf0

theorem stand_wk : FA2.stand wk = 4 := rfl
theorem kopf_wk : FA2.kopfSt wk = 1 := rfl
theorem naechst_wk (j : Int) : FA2.naechst wk j = 4 := rfl
theorem lg_wk : LG2.st wk = 2 := rfl
theorem wz_wk : Wz2.st wk = 0 := rfl
theorem ll_wk (j : Int) : LL2.wert wk j = 4 := by show max 0 (min 4 (nilF j)) = 4; unfold nilF; decide
theorem lf_wk (j : Int) : Lf2.wert wk j = 4 := by show max 0 (min 4 (nilF j)) = 4; unfold nilF; decide
theorem rf_wk (j : Int) : Rf2.wert wk j = rf0 j := by
  show max 0 (min 4 (rf0 j)) = rf0 j
  unfold rf0; split <;> omega

theorem kette_wk : FA2.Kette wk 1 [1] :=
  FreiForm.Kette.cons 1 (by decide) (by decide) [] (by rw [naechst_wk]; exact FreiForm.Kette.nil)

theorem freiOk_wk : FA2.FreiOk wk := by
  refine ⟨[1], by rw [kopf_wk]; exact kette_wk, by decide, ?_⟩
  intro i hi; simp at hi; subst hi; rw [stand_wk]; omega

theorem aufListe_wk (i : Int) : FA2.AufListe wk i ↔ i = 1 := by
  constructor
  · rintro ⟨L, hL, hm⟩
    rw [kopf_wk] at hL
    have := FreiForm.Kette.eindeutig hL kette_wk
    subst this; simpa using hm
  · rintro rfl
    exact ⟨[1], by rw [kopf_wk]; exact kette_wk, by simp⟩

theorem lebt_wk (i : Int) : FA2.Lebt wk i ↔ (0 ≤ i ∧ i < 4 ∧ i ≠ 1) := by
  unfold FreiForm.Lebt
  rw [aufListe_wk, stand_wk]

theorem listeKette_wk : KetteF 4 (LL2.wert wk) 2 [2] := by
  refine KetteF.cons 2 (by decide) (by decide) [] ?_
  rw [ll_wk]
  exact KetteF.nil

theorem listOk_wk : ListOk FA2 LL2 LG2 wk := by
  unfold ListOk
  rw [lg_wk]
  refine ⟨[2], listeKette_wk, by decide, ?_⟩
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  subst hi
  exact (lebt_wk _).mpr (by decide)

theorem baumF_wk : BaumF 4 (Lf2.wert wk) (Rf2.wert wk) 0 [0, 3] := by
  have h3 : BaumF 4 (Lf2.wert wk) (Rf2.wert wk) 3 [3] := by
    have := BaumF.node (c := 4) (l := Lf2.wert wk) (r := Rf2.wert wk) 3 (by decide) (by decide) [] []
      (by rw [lf_wk]; exact BaumF.nil) (by rw [rf_wk]; exact BaumF.nil)
    simpa using this
  have := BaumF.node (c := 4) (l := Lf2.wert wk) (r := Rf2.wert wk) 0 (by decide) (by decide) [] [3]
    (by rw [lf_wk]; exact BaumF.nil) (by rw [rf_wk]; exact h3)
  simpa using this

theorem baumOk_wk : BaumOk FA2 Lf2 Rf2 Wz2 wk := by
  unfold BaumOk
  rw [wz_wk]
  refine ⟨[0, 3], baumF_wk, by decide, ?_⟩
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact (lebt_wk _).mpr (by decide)
  · exact (lebt_wk _).mpr (by decide)

/-- **The scenario world meets the invariant of the arena:** free list, list `2`, tree `0 (right 3)`, and no slot in both. -/
theorem ok_wk : K2.Ok wk := by
  refine ⟨freiOk_wk, (Dekl.LOk_some (K := K2) (d := ⟨LL2, LG2⟩) rfl wk).mpr listOk_wk,
    (Dekl.BOk_some (K := K2) (b := ⟨Lf2, Rf2, Wz2, by decide⟩) rfl wk).mpr baumOk_wk, ?_⟩
  rintro j ⟨hL, hB⟩
  obtain ⟨L, hL', hm⟩ := (Dekl.InL_some (K := K2) (d := ⟨LL2, LG2⟩) rfl wk j).mp hL
  rw [lg_wk] at hL'
  have h1 := KetteF.eindeutig hL' listeKette_wk
  subst h1
  obtain ⟨S, hS, hm2⟩ := (Dekl.InB_some (K := K2) (b := ⟨Lf2, Rf2, Wz2, by decide⟩) rfl wk j).mp hB
  rw [wz_wk] at hS
  have h2 := BaumF.eindeutig hS baumF_wk
  subst h2
  simp at hm hm2
  omega

/-- A world that meets the arena invariant has a well formed list and tree. -/
theorem listOk_von {σ : World FD2} (h : K2.Ok σ) : ListOk FA2 LL2 LG2 σ :=
  (Dekl.LOk_some (K := K2) (d := ⟨LL2, LG2⟩) rfl σ).mp h.2.1

theorem baumOk_von {σ : World FD2} (h : K2.Ok σ) : BaumOk FA2 Lf2 Rf2 Wz2 σ :=
  (Dekl.BOk_some (K := K2) (b := ⟨Lf2, Rf2, Wz2, by decide⟩) rfl σ).mp h.2.2.1

/-! ### The contract, the oracle and the bodies' small helpers -/

def FV2 : Vertrag FD2 where
  schreibt := fun _ => true
  gschreibt := fun _ => true
  erg := none
  gruende := 0
  haelt := []
  produziert := []

theorem fdarf2 : darf FD2 () ([] : List (Res FD2)) := by
  intro w hw; cases hw

theorem fgdarf2 (g : FD2.Glob) : gdarf FD2 g ([] : List (Res FD2)) := by
  intro w hw; cases hw

/-- The payload `7`, at the payload field's declared type. -/
def sieben2 : Expr FD2 [] [] (FD2.typ FA2.tab FA2.feld) :=
  Expr.umTyp (show Ty.int 0 255 = FD2.typ FA2.tab FA2.feld from by decide)
    (Expr.widen (by decide) (by decide) (Expr.lit 7))

def oF2 : Orakel FD2 where
  wirkt := fun a => nomatch a
  regLies := fun r => nomatch r
  regSchreib := fun r => nomatch r
  sichtbar := fun _ _ => false

def rF2 : ∀ f : FD2.Fn, World FD2 → Env FD2 (FD2.params f) → RufAusgang f := fun _ _ _ => .logik .vorzustand

abbrev G1k : Ctx := [Ty.index (FD2.count FA2.tab)]
abbrev G2k : Ctx := [Ty.index (FD2.count FA2.tab), Ty.index (FD2.count FA2.tab)]
abbrev G3k : Ctx :=
  [Ty.index (FD2.count FA2.tab), Ty.index (FD2.count FA2.tab), Ty.index (FD2.count FA2.tab)]

def vollK0 : Endblock FD2 FV2 false [] [] := Endblock.ret ErgExpr.empty (List.Perm.refl _)
def vollK1 : Endblock FD2 FV2 false G1k [] := Endblock.ret ErgExpr.empty (List.Perm.refl _)
def vollK2 : Endblock FD2 FV2 false G2k [] := Endblock.ret ErgExpr.empty (List.Perm.refl _)
def vollK3 : Endblock FD2 FV2 false G3k [] := Endblock.ret ErgExpr.empty (List.Perm.refl _)
theorem rein_vollK0 : Rein vollK0 := Rein.ret _ _
theorem rein_vollK1 : Rein vollK1 := Rein.ret _ _
theorem rein_vollK2 : Rein vollK2 := Rein.ret _ _
theorem rein_vollK3 : Rein vollK3 := Rein.ret _ _

/-- The run of a body, named: a long run is stated through an equation, not unfolded by the elaborator. -/
theorem lauf_post {l : Bool} {Γ : Ctx} {a' : Abs} {b : Block FD2 FV2 l Γ [] []} (h : Erk K2 Abs.leer b a')
    (σ : World FD2) (ρ : Env FD2 Γ) (hS : K2.Ok σ) {o : Ausgang FV2 l Γ}
    (ho : execBlock oF2 0 rF2 b σ ρ = o) : StrukturPost K2 a' o :=
  erk_koerper_lauf oF2 0 rF2 K2 h σ ρ hS ho

/-! ### Accepted: a tree move and a list read in one body -/

/-- Take slot `1` off the free list, read the root, hang the slot at the left place of the root, read the list head. -/
def kombiHang : Block FD2 FV2 false [] [] [] :=
  Block.freiNimm FA2 sieben2 rfl fdarf2 rfl (fgdarf2 _) vollK0
    (Block.linkKopfBind Wz2 (fgdarf2 _) vollK1
      (Block.haengen Lf2 Rf2 (.here : Var G2k _) (.there .here : Var G2k _) rfl fdarf2 vollK2
        (Block.linkKopfBind LG2 (fgdarf2 _) vollK2 .nil)))

/-- **The recognizer accepts it** -- from a state that knows nothing. -/
theorem erk_kombiHang : ∃ a' : Abs, Erk K2 Abs.leer kombiHang a' :=
  ⟨_, Erk.nimm sieben2 rfl fdarf2 rfl (fgdarf2 _) vollK0 _ rein_vollK0
    (Erk.wurzelKopf ⟨Lf2, Rf2, Wz2, by decide⟩ rfl (fgdarf2 _) vollK1 _ rein_vollK1
      (Erk.haengen ⟨Lf2, Rf2, Wz2, by decide⟩ rfl Lf2 Rf2 (Or.inl ⟨rfl, rfl⟩) (.here : Var G2k _)
        (.there .here : Var G2k _) rfl fdarf2 vollK2 _ (by simp [Abs.ext, Var.pos])
        (by simp [Abs.ext, Var.pos]) rein_vollK2
        (Erk.kopf ⟨LL2, LG2⟩ rfl (fgdarf2 _) vollK2 .nil rein_vollK2 (Erk.nil _))))⟩

def kombiHangOk : Bool :=
  match execBlock (V := FV2) oF2 0 rF2 kombiHang wk .nil with
  | .ok σ' _ => decide (Lf2.wert σ' 0 = 1 ∧ Rf2.wert σ' 0 = 3 ∧ LG2.st σ' = 2 ∧ FA2.kopfSt σ' = 4)
  | _ => false

theorem kombiHangOk_wahr : kombiHangOk = true := by decide +kernel

/-- **Run on the real world:** the tree `0 (right 3)` gets the left child `1` (the slot that came off the free list), the
    list `2` is as it was, the free list is empty, and the invariant of the arena holds -- as the recognizer promised. -/
theorem kombiHang_zeuge : ∃ σ' : World FD2, execBlock (V := FV2) oF2 0 rF2 kombiHang wk .nil = .ok σ' .nil ∧
    K2.Ok σ' ∧ Lf2.wert σ' 0 = 1 ∧ Rf2.wert σ' 0 = 3 ∧ LG2.st σ' = 2 ∧ FA2.kopfSt σ' = 4 := by
  obtain ⟨a', h⟩ := erk_kombiHang
  have hd := kombiHangOk_wahr
  unfold kombiHangOk at hd
  revert hd
  generalize hx : execBlock (V := FV2) oF2 0 rF2 kombiHang wk .nil = o
  have hpost := lauf_post h wk .nil ok_wk hx
  cases o with
  | ok σ' ρ =>
    intro hd
    cases ρ
    simp only [decide_eq_true_eq] at hd
    exact ⟨σ', rfl, hpost.1, hd⟩
  | zurueck _ _ => intro hd; exact absurd hd (by simp)
  | why _ _ => intro hd; exact absurd hd (by simp)
  | leave _ _ _ => intro hd; exact absurd hd (by simp)
  | next _ _ _ => intro hd; exact absurd hd (by simp)
  | logik _ => intro hd; exact absurd hd (by simp)
  | hardware _ => intro hd; exact absurd hd (by simp)

/-! ### Accepted: a slot moves from the tree to the list -/

/-- Read the root, cut its right child (a leaf) off the tree, link it in at the head of the list. -/
def kombiVersetzen : Block FD2 FV2 false [] [] [] :=
  Block.linkKopfBind Wz2 (fgdarf2 _) vollK0
    (Block.abschneiden Lf2 Rf2 Rf2 (.here : Var G1k _) rfl fdarf2 vollK1 vollK2
      (Block.linkPush LL2 LG2 (.here : Var G2k _) rfl fdarf2 rfl (fgdarf2 _) .nil))

theorem erk_kombiVersetzen : ∃ a' : Abs, Erk K2 Abs.leer kombiVersetzen a' :=
  ⟨_, Erk.wurzelKopf ⟨Lf2, Rf2, Wz2, by decide⟩ rfl (fgdarf2 _) vollK0 _ rein_vollK0
    (Erk.abschneiden ⟨Lf2, Rf2, Wz2, by decide⟩ rfl Rf2 (Or.inr rfl) (.here : Var G1k _) rfl fdarf2 vollK1
      vollK2 _ (by simp [Abs.ext, Var.pos]) rein_vollK1 rein_vollK2
      (Erk.push ⟨LL2, LG2⟩ rfl (.here : Var G2k _) rfl fdarf2 rfl (fgdarf2 _) .nil
        (by simp [Abs.forget, Abs.ext, Var.pos]) (Erk.nil _)))⟩

def kombiVersetzenOk : Bool :=
  match execBlock (V := FV2) oF2 0 rF2 kombiVersetzen wk .nil with
  | .ok σ' _ => decide (Rf2.wert σ' 0 = 4 ∧ LG2.st σ' = 3 ∧ LL2.wert σ' 3 = 2 ∧ Wz2.st σ' = 0)
  | _ => false

theorem kombiVersetzenOk_wahr : kombiVersetzenOk = true := by decide +kernel

/-- **Run on the real world:** the leaf `3` leaves the tree and becomes the head of the list `3 -> 2`; the tree is the root
    alone; the arena invariant (both structures well formed, no slot in both) holds. -/
theorem kombiVersetzen_zeuge : ∃ σ' : World FD2, execBlock (V := FV2) oF2 0 rF2 kombiVersetzen wk .nil = .ok σ' .nil ∧
    K2.Ok σ' ∧ Rf2.wert σ' 0 = 4 ∧ LG2.st σ' = 3 ∧ LL2.wert σ' 3 = 2 ∧ Wz2.st σ' = 0 := by
  obtain ⟨a', h⟩ := erk_kombiVersetzen
  have hd := kombiVersetzenOk_wahr
  unfold kombiVersetzenOk at hd
  revert hd
  generalize hx : execBlock (V := FV2) oF2 0 rF2 kombiVersetzen wk .nil = o
  have hpost := lauf_post h wk .nil ok_wk hx
  cases o with
  | ok σ' ρ =>
    intro hd
    cases ρ
    simp only [decide_eq_true_eq] at hd
    exact ⟨σ', rfl, hpost.1, hd⟩
  | zurueck _ _ => intro hd; exact absurd hd (by simp)
  | why _ _ => intro hd; exact absurd hd (by simp)
  | leave _ _ _ => intro hd; exact absurd hd (by simp)
  | next _ _ _ => intro hd; exact absurd hd (by simp)
  | logik _ => intro hd; exact absurd hd (by simp)
  | hardware _ => intro hd; exact absurd hd (by simp)

/-! ### Planted defect: a slot in both structures -/

/-- Read the root and link it into the list. -/
def doppelGlied : Block FD2 FV2 false [] [] [] :=
  Block.linkKopfBind Wz2 (fgdarf2 _) vollK0
    (Block.linkPush LL2 LG2 (.here : Var G1k _) rfl fdarf2 rfl (fgdarf2 _) .nil)

def doppelGliedOk : Bool :=
  match execBlock (V := FV2) oF2 0 rF2 doppelGlied wk .nil with
  | .ok σ' _ => decide (LG2.st σ' = 0 ∧ Wz2.st σ' = 0)
  | _ => false

theorem doppelGliedOk_wahr : doppelGliedOk = true := by decide +kernel

/-- **A slot in both structures has no derivation:** run on `wk`, the root `0` becomes the head of the list while it is
    still the root of the tree. The list is well formed, the tree is well formed -- and the slot is a member of both, which
    the arena invariant forbids. -/
theorem doppelGlied_abgelehnt (a' : Abs) : ¬ Erk K2 Abs.leer doppelGlied a' := by
  intro h
  have hd := doppelGliedOk_wahr
  unfold doppelGliedOk at hd
  revert hd
  generalize hx : execBlock (V := FV2) oF2 0 rF2 doppelGlied wk .nil = o
  have hpost := lauf_post h wk .nil ok_wk hx
  cases o with
  | ok σ' ρ =>
    intro hd
    simp only [decide_eq_true_eq] at hd
    have hl := listOk_von hpost.1
    have hb := baumOk_von hpost.1
    have hinL : K2.InL σ' 0 := by
      refine (Dekl.InL_some (K := K2) (d := ⟨LL2, LG2⟩) rfl σ' 0).mpr ?_
      have := kopf_auf hl (by show LG2.st σ' < 4; rw [hd.1]; decide)
      show Auf (FD2.count FA2.tab) (LL2.wert σ') (LG2.st σ') 0
      rw [hd.1]
      rw [hd.1] at this
      exact this
    have hinB : K2.InB σ' 0 := by
      refine (Dekl.InB_some (K := K2) (b := ⟨Lf2, Rf2, Wz2, by decide⟩) rfl σ' 0).mpr ?_
      have hb' : BaumOkF 4 (Lf2.wert σ') (Rf2.wert σ') 0 (FA2.Lebt σ') := by
        have := hb; unfold BaumOk at this; rwa [hd.2] at this
      have := ArenaKette.InBaum.wurzel hb' (by decide)
      show InBaum (FD2.count FA2.tab) (Lf2.wert σ') (Rf2.wert σ') (Wz2.st σ') 0
      rw [hd.2]
      exact this
    exact hpost.1.2.2.2 0 ⟨hinL, hinB⟩
  | zurueck _ _ => intro hd; exact absurd hd (by simp)
  | why _ _ => intro hd; exact absurd hd (by simp)
  | leave _ _ _ => intro hd; exact absurd hd (by simp)
  | next _ _ _ => intro hd; exact absurd hd (by simp)
  | logik _ => intro hd; exact absurd hd (by simp)
  | hardware _ => intro hd; exact absurd hd (by simp)

end ErkKombi

end Gabbro.Grammatik

#print axioms Gabbro.Grammatik.ErkKombi.ok_wk
#print axioms Gabbro.Grammatik.ErkKombi.erk_kombiHang
#print axioms Gabbro.Grammatik.ErkKombi.kombiHang_zeuge
#print axioms Gabbro.Grammatik.ErkKombi.erk_kombiVersetzen
#print axioms Gabbro.Grammatik.ErkKombi.kombiVersetzen_zeuge
#print axioms Gabbro.Grammatik.ErkKombi.doppelGlied_abgelehnt
