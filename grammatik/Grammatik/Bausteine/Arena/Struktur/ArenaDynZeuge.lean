/-
  File:      Grammatik/ArenaDynZeuge.lean
  Subject:   WITNESSES AND PLANTED DEFECTS for `InvDyn` (PLAN-DYNAMIC.md section 8a, phase 2): a concrete
             arena with slot release in which a list and a tree of live slots exist, a slot is on the free
             list, and the mutators of `ArenaListe.lean` / `ArenaBaumWelt.lean` are applied to real worlds.

  The declaration: one table of four slots (nil marker `4`), fields `feld` (payload byte), `nxt` (free link),
  `lnk` (list link / left child), `rgt` (right child); four words `zaehl`, `komm`, `kopf` (free list head),
  `lkopf` (list head / tree root). Worlds are built by `wd` from the four words and the three link functions.

  Scenario: three slots handed out (`stand = 3`), slot `1` released (free list `[1]`), slots `0` and `2` live and
  linked `2 -> 0` (list) respectively `2` the root with the single child `0` (tree). The planted defect: the same
  list while slot `2` is ALSO on the free list -- the model rejects it (`liste_defekt_bricht`).
-/
import Grammatik.Bausteine.Arena.Struktur.ArenaBaumWelt

namespace Gabbro.Grammatik

open Gabbro.Grammatik.ArenaDyn Gabbro.Grammatik.ArenaKette

namespace InvDynZeuge

/-- A byte or an index word, clamped into range so that no proof is needed to name a value. -/
def zc (v : Int) : Zahl 0 4 := ⟨max 0 (min 4 v), by omega, by omega⟩

@[reducible] def FD : Deklaration where
  Tab := Unit
  decTab := inferInstance
  count := fun _ => 4
  Feld := fun _ => Fin 4
  decFeld := fun _ => inferInstance
  typ := fun _ f => if f = 0 then .int 0 255 else .int 0 4
  erlaubt := fun _ _ _ _ => false
  tabNr := fun | 0 => some () | _ => none
  Glob := Fin 4
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
  geteilt_bewacht := fun t h => by simp only [Bool.false_eq_true] at h
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun g h => by simp only [Bool.false_eq_true] at h

/-- The arena with slot release: payload `0`, free link `1`; words `0` (counter), `1` (committed), `2` (free head). -/
def FA : FreiForm FD where
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
def LL : LinkFeld FA where
  f := 2
  hf := rfl
  h1 := by decide
  h2 := by decide

def LG : LinkKopf FA where
  g := 3
  hg := rfl
  h1 := by decide
  h2 := by decide
  h3 := by decide

/-- The right child link (field `3`). -/
def RR : LinkFeld FA where
  f := 3
  hf := rfl
  h1 := by decide
  h2 := by decide

/-- A world from the counter, the free head, the list head / tree root, the free links, the left links, the right links. -/
def wd (st kopf lk : Int) (nx ln rn : Int → Int) : World FD where
  slots := fun _ k f =>
    if h0 : f = 0 then (by subst h0; exact (⟨0, by decide, by decide⟩ : Zahl 0 255))
    else if h1 : f = 1 then (by
      have : FD.typ () f = .int 0 4 := by simp only [Fin.isValue, h0, ↓reduceIte]
      rw [this]; exact zc (nx k))
    else if h2 : f = 2 then (by
      have : FD.typ () f = .int 0 4 := by simp only [Fin.isValue, h0, ↓reduceIte]
      rw [this]; exact zc (ln k))
    else (by
      have : FD.typ () f = .int 0 4 := by simp only [Fin.isValue, h0, ↓reduceIte]
      rw [this]; exact zc (rn k))
  globs := fun g =>
    if g = 0 then zc st else if g = 1 then zc st else if g = 2 then zc kopf else zc lk
  spur := []

/-- Slot `1` is released (free list `[1]`), nothing else is. -/
def nx0 : Int → Int := fun _ => 4
/-- The list `2 -> 0`. -/
def ln0 : Int → Int := fun k => if k = 2 then 0 else 4
/-- The tree: `2` has the left child `0`. -/
def rn0 : Int → Int := fun _ => 4

def w0 : World FD := wd 4 1 2 nx0 ln0 rn0

theorem stand_w0 : FA.stand w0 = 4 := rfl
theorem kopf_w0 : FA.kopfSt w0 = 1 := rfl
theorem naechst_w0 (j : Int) : FA.naechst w0 j = 4 := rfl
theorem lg_w0 : LG.st w0 = 2 := rfl
theorem ll_w0 (j : Int) : LL.wert w0 j = ln0 j := by
  show max 0 (min 4 (ln0 j)) = ln0 j
  unfold ln0; split <;> omega
theorem rr_w0 (j : Int) : RR.wert w0 j = 4 := rfl

/-- The free list of the scenario is `[1]`: not empty, so the allocator has a slot to hand out. -/
theorem kette_w0 : FA.Kette w0 1 [1] :=
  FreiForm.Kette.cons 1 (by decide) (by decide) [] (by rw [naechst_w0]; exact FreiForm.Kette.nil)

theorem freiOk_w0 : FA.FreiOk w0 := by
  refine ⟨[1], by rw [kopf_w0]; exact kette_w0, by decide, ?_⟩
  intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; subst hi; rw [stand_w0]; omega

theorem aufListe_w0 (i : Int) : FA.AufListe w0 i ↔ i = 1 := by
  constructor
  · rintro ⟨L, hL, hm⟩
    rw [kopf_w0] at hL
    have := FreiForm.Kette.eindeutig hL kette_w0
    subst this; simpa using hm
  · rintro rfl
    exact ⟨[1], by rw [kopf_w0]; exact kette_w0, by simp only [List.mem_cons, List.not_mem_nil, or_false]⟩

theorem lebt_w0 (i : Int) : FA.Lebt w0 i ↔ (0 ≤ i ∧ i < 4 ∧ i ≠ 1) := by
  unfold FreiForm.Lebt
  rw [aufListe_w0, stand_w0]

/-- Slot `1` is dead (on the free list); `0`, `2`, `3` are live: the scenario separates the two. -/
theorem lebt_unterschied : FA.Lebt w0 0 ∧ FA.Lebt w0 2 ∧ FA.Lebt w0 3 ∧ ¬ FA.Lebt w0 1 := by
  refine ⟨(lebt_w0 0).mpr (by decide), (lebt_w0 2).mpr (by decide), (lebt_w0 3).mpr (by decide), ?_⟩
  intro h; have := ((lebt_w0 1).mp h).2.2; exact this rfl

/-! ### The list `2 -> 0` -/

theorem listeKette_w0 : KetteF 4 (LL.wert w0) 2 [2, 0] := by
  refine KetteF.cons 2 (by decide) (by decide) [0] ?_
  rw [ll_w0]
  refine KetteF.cons 0 (by decide) (by decide) [] ?_
  rw [ll_w0]
  exact KetteF.nil

theorem listOk_w0 : ListOk FA LL LG w0 := by
  unfold ListOk
  rw [lg_w0]
  refine ⟨[2, 0], listeKette_w0, by decide, ?_⟩
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact (lebt_w0 _).mpr (by decide)
  · exact (lebt_w0 _).mpr (by decide)

/-- The head of the list, after `pop`: slot `0`. -/
def w1 : World FD := wd 4 1 0 nx0 ln0 rn0

/-- **`pop` on a real world:** the hypotheses of `liste_pop` hold, the conclusion is the invariant of the shorter list,
    the popped slot `2` is live and no longer linked -- and it is NOT on the free list, so `free` may follow. -/
theorem pop_zeuge :
    ListOk FA LL LG w1 ∧ ¬ Auf 4 (LL.wert w1) (LG.st w1) 2 ∧ FA.Lebt w1 2 := by
  have h := liste_pop FA LL LG listOk_w0 (by rw [lg_w0]; decide) (hk := rfl) (hn := fun j => rfl) (hs := rfl)
    (σ' := w1) (by rw [lg_w0, ll_w0]; rfl) (fun j => rfl)
  rw [lg_w0] at h
  exact h

/-- The list is not degenerate after the pop: it holds exactly the slot `0`. -/
theorem pop_kette : KetteF 4 (LL.wert w1) 0 [0] := by
  refine KetteF.cons 0 (by decide) (by decide) [] ?_
  have : LL.wert w1 0 = 4 := by show max 0 (min 4 (ln0 0)) = 4; decide
  rw [this]; exact KetteF.nil

/-! ### The planted defect: a slot on the list AND on the free list -/

/-- Slot `2` is linked in the list and ALSO on the free list. -/
def wBad : World FD := wd 4 2 2 nx0 ln0 rn0

theorem aufListe_bad : FA.AufListe wBad 2 :=
  ⟨[2], FreiForm.Kette.cons 2 (by decide) (by decide) [] FreiForm.Kette.nil, by simp only [List.mem_cons, List.not_mem_nil, or_false]⟩

/-- **The model rejects it:** a list slot that is also on the free list is not live, so `ListOk` fails. The checker's
    refusal of a use after release (`N586`) is what keeps real programs out of this state. -/
theorem liste_defekt_bricht : ¬ ListOk FA LL LG wBad := by
  intro h
  unfold ListOk at h
  have hk := h
  obtain ⟨L, hk0, _, _⟩ := hk
  have hne : LG.st wBad < 4 := by decide
  have := h.lebt_auf (auf_kopf hne ⟨L, hk0⟩)
  exact this.2.2 aufListe_bad

/-! ### The tree `2 (left 0)` and a leaf in at the right -/

theorem baumB_w0 : BaumF 4 (LL.wert w0) (RR.wert w0) 2 [2, 0] := by
  have hl : LL.wert w0 2 = 0 := by rw [ll_w0]; rfl
  have h0 : BaumF 4 (LL.wert w0) (RR.wert w0) 0 [0] := by
    have := BaumF.node (c := 4) (l := LL.wert w0) (r := RR.wert w0) 0 (by decide) (by decide) [] []
      (by rw [ll_w0]; exact BaumF.nil) (by rw [rr_w0]; exact BaumF.nil)
    simpa using this
  have := BaumF.node (c := 4) (l := LL.wert w0) (r := RR.wert w0) 2 (by decide) (by decide) [0] []
    (by rw [hl]; exact h0) (by rw [rr_w0]; exact BaumF.nil)
  simpa using this

theorem baumOk_w0 : BaumOk FA LL RR LG w0 := by
  unfold BaumOk
  rw [lg_w0]
  refine ⟨[2, 0], baumB_w0, by decide, ?_⟩
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact (lebt_w0 _).mpr (by decide)
  · exact (lebt_w0 _).mpr (by decide)

def rn2 : Int → Int := fun k => if k = 2 then 3 else 4

/-- The tree after hanging the live slot `3` at the right of `2`. -/
def w2 : World FD := wd 4 1 2 nx0 ln0 rn2

theorem rr_w2 (j : Int) : RR.wert w2 j = rn2 j := by
  show max 0 (min 4 (rn2 j)) = rn2 j
  unfold rn2; split <;> omega

/-- **Leaf in on a real world:** the live, unlinked slot `3` becomes the right child of the root `2`. -/
theorem einfuegen_zeuge :
    BaumOk FA LL RR LG w2 ∧ InBaum 4 (LL.wert w2) (RR.wert w2) (LG.st w2) 3 := by
  have hnot : ¬ InBaum 4 (LL.wert w0) (RR.wert w0) (LG.st w0) 3 := by
    rintro ⟨S, hS, hm⟩
    rw [lg_w0] at hS
    have := BaumF.eindeutig hS baumB_w0
    subst this; simp only [List.mem_cons, Int.reduceEq, List.not_mem_nil, or_self] at hm
  have hp : InBaum 4 (LL.wert w0) (RR.wert w0) (LG.st w0) 2 := by
    rw [lg_w0]; exact ⟨[2, 0], baumB_w0, by simp only [List.mem_cons, Int.reduceEq, List.not_mem_nil, or_self, or_false]⟩
  have h := baum_einfuegen_rechts FA LL RR LG baumOk_w0 (σ' := w2) 2 3 hp (by rw [rr_w0])
    ((lebt_w0 3).mpr (by decide)) hnot rfl (fun j => rfl) rfl rfl
    (by simp only [rr_w2, rn2, ↓reduceIte]) (by simp only [rr_w2, rn2, Int.reduceEq, ↓reduceIte])
    (by show max 0 (min 4 (ln0 3)) = 4; decide)
    (fun j hj hji => by rw [rr_w2, rr_w0]; unfold rn2; simp only [hj, ↓reduceIte])
    (fun j hji => rfl)
  exact h

/-! ### An executed run: `alloc` from the free list on the real world -/

/-- The contract of the witness body: it writes the table and every word. -/
def FV : Vertrag FD where
  schreibt := fun _ => true
  gschreibt := fun _ => true
  erg := none
  gruende := 0
  haelt := []
  produziert := []

theorem fdarf : darf FD () ([] : List (Res FD)) := by
  intro w hw; cases hw

theorem fgdarf (g : FD.Glob) : gdarf FD g ([] : List (Res FD)) := by
  intro w hw; cases hw

/-- The payload `7`, at the payload field's declared type. -/
def sieben : Expr FD [] [] (FD.typ FA.tab FA.feld) :=
  Expr.umTyp (show Ty.int 0 255 = FD.typ FA.tab FA.feld from by decide)
    (Expr.widen (by decide) (by decide) (Expr.lit 7))

/-- **`alloc` from the free list, executed, on the real world `w0`:** slot `1` comes off the free list, the free list is
    empty afterwards (`FreiOk` holds for a list of length zero), the list `2 -> 0` is untouched, and the slot is live
    and not linked. Both the list and the free list are non-empty before, so no clause is vacuous. -/
theorem nimm_zeuge (O : Orakel FD) (passes : Nat)
    (R : ∀ f : FD.Fn, World FD → Env FD (FD.params f) → RufAusgang f)
    (voll : Endblock FD FV false [] []) :
    ∃ σ' : World FD,
      execBlock (V := FV) O passes R
          (Block.freiNimm (Λ' := []) FA sieben rfl fdarf rfl (fgdarf _) voll .nil) w0 .nil = .ok σ' .nil ∧
      FA.FreiOk σ' ∧ ListOk FA LL LG σ' ∧ FA.Lebt σ' 1 ∧ ¬ Auf 4 (LL.wert σ') (LG.st σ') 1 := by
  have h := liste_nimm O passes R (l := false) (Γ := []) (Λ := []) FA LL LG sieben rfl fdarf rfl (fgdarf _) voll w0 .nil
    (by rw [kopf_w0]; decide) freiOk_w0 listOk_w0
  rw [kopf_w0] at h
  exact h

end InvDynZeuge

#print axioms Gabbro.Grammatik.InvDynZeuge.liste_defekt_bricht
#print axioms Gabbro.Grammatik.InvDynZeuge.pop_zeuge
#print axioms Gabbro.Grammatik.InvDynZeuge.einfuegen_zeuge
#print axioms Gabbro.Grammatik.InvDynZeuge.nimm_zeuge
#print axioms Gabbro.Grammatik.InvDynZeuge.listOk_w0
#print axioms Gabbro.Grammatik.InvDynZeuge.baumOk_w0
#print axioms Gabbro.Grammatik.InvDynZeuge.freiOk_w0
#print axioms Gabbro.Grammatik.InvDynZeuge.lebt_unterschied

end Gabbro.Grammatik
