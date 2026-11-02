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
module
public import Grammatik.Bausteine.Arena.Struktur.Erkenner.ArenaErkennerZeuge
@[expose] public section


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
      have : FD2.typ () f = .int 0 4 := by simp only [Fin.isValue, h0, ↓reduceIte]
      rw [this]; exact InvDynZeuge.zc (nx k))
    else if h2 : f = 2 then (by
      have : FD2.typ () f = .int 0 4 := by simp only [Fin.isValue, h0, ↓reduceIte]
      rw [this]; exact InvDynZeuge.zc (ln k))
    else if h3 : f = 3 then (by
      have : FD2.typ () f = .int 0 4 := by simp only [Fin.isValue, h0, ↓reduceIte]
      rw [this]; exact InvDynZeuge.zc (lf k))
    else (by
      have : FD2.typ () f = .int 0 4 := by simp only [Fin.isValue, h0, ↓reduceIte]
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

theorem stand_wk : FA2.stand wk = 4 := by rfl
theorem kopf_wk : FA2.kopfSt wk = 1 := by rfl
theorem naechst_wk (j : Int) : FA2.naechst wk j = 4 := by rfl
theorem lg_wk : LG2.st wk = 2 := by rfl
theorem wz_wk : Wz2.st wk = 0 := by rfl
theorem ll_wk (j : Int) : LL2.wert wk j = 4 := by show max 0 (min 4 (nilF j)) = 4; unfold nilF; decide
theorem lf_wk (j : Int) : Lf2.wert wk j = 4 := by show max 0 (min 4 (nilF j)) = 4; unfold nilF; decide
theorem rf_wk (j : Int) : Rf2.wert wk j = rf0 j := by
  show max 0 (min 4 (rf0 j)) = rf0 j
  unfold rf0; split <;> omega

theorem kette_wk : FA2.Kette wk 1 [1] :=
  FreiForm.Kette.cons 1 (by decide) (by decide) [] (by rw [naechst_wk]; exact FreiForm.Kette.nil)

theorem freiOk_wk : FA2.FreiOk wk := by
  refine ⟨[1], by rw [kopf_wk]; exact kette_wk, by decide, ?_⟩
  intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; subst hi; rw [stand_wk]; omega

theorem aufListe_wk (i : Int) : FA2.AufListe wk i ↔ i = 1 := by
  constructor
  · rintro ⟨L, hL, hm⟩
    rw [kopf_wk] at hL
    have := FreiForm.Kette.eindeutig hL kette_wk
    subst this; simpa using hm
  · rintro rfl
    exact ⟨[1], by rw [kopf_wk]; exact kette_wk, by simp only [List.mem_cons, List.not_mem_nil, or_false]⟩

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

end ErkKombi
end Gabbro.Grammatik
